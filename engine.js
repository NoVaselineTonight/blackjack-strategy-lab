/* Blackjack expected-value engine.
 * Exact recursive calculation over the remaining shoe (composition dependent).
 * Ranks: 1 = Ace, 2..9, 10 = any ten-value card.
 * Split hands use the standard approximation: every split hand draws from the
 * shoe with the pair cards and the upcard removed, and resplits are handled with
 * a pending-hands recursion.
 */
(function (global) {
  'use strict';

  const P32 = [0];
  for (let i = 1; i <= 10; i++) P32[i] = Math.pow(32, i - 1);

  const DEFAULT_RULES = {
    decks: 6,              // 0 = infinite deck
    h17: false,            // dealer hits soft 17
    holeCard: 'peek',      // 'peek' | 'enhc' (lose all to dealer BJ) | 'enhc_obo' (original bet only)
    bjPay: 1.5,
    insurance: true,
    insurancePay: 2,
    doubleRule: 'any',     // 'any' | '9-11' | '10-11' | '11'
    doubleAnyCards: false, // double after hitting
    das: true,
    maxHands: 4,           // 1 = no splitting
    resplitAces: false,
    splitAces: 'one',      // 'one' | 'hit' | 'hitdouble'
    splitAceTenBJ: false,
    surrender: 'none',     // 'none' | 'late' | 'early'
    charlie: 0,            // 0 = off, else number of cards
    dealer22Push: false,
    freeDouble: false,     // Free Bet: free doubles on hard 9, 10, 11
    freeSplit: false,      // Free Bet: free splits on all pairs except tens
    penetration: 0.75
  };

  const LEAF = [];
  for (let i = 0; i < 7; i++) { const a = new Float64Array(8); a[i] = 1; LEAF.push(a); }

  function createEngine(rules) {
    const R = Object.assign({}, DEFAULT_RULES, rules);
    const inf = !R.decks;
    const D = inf ? 1 : R.decks;
    const base = new Array(11).fill(0);
    for (let c = 1; c <= 10; c++) base[c] = (c === 10 ? 16 : 4) * D;
    const N = 52 * D;
    // Memo keys pack removed counts per rank; the radix must exceed any count a rank can reach.
    const RAD = Math.max(32, 4 * D + 1);
    const P32 = [0];
    for (let i = 1; i <= 10; i++) P32[i] = Math.pow(RAD, i - 1);
    const cond = R.holeCard !== 'enhc'; // condition on "dealer has no blackjack"

    const rm = new Array(11).fill(0);
    let rmN = 0, rkey = 0, U = 1;
    let dealerMemo = [], playerMemo = [];
    for (let u = 0; u <= 10; u++) { dealerMemo.push(new Map()); playerMemo.push(new Map()); }

    function add(c) { if (rm[c] >= base[c]) over++; rm[c]++; rmN++; rkey += P32[c]; }
    function del(c) { rm[c]--; rmN--; rkey -= P32[c]; if (rm[c] >= base[c]) over--; }
    let over = 0; // cards removed beyond what a rank holds; they are not in the shoe either way
    function prob(c) {
      if (inf) return base[c] / N;
      const k = base[c] - rm[c];
      return k > 0 ? k / (N - rmN + over) : 0;
    }
    function bestTotal(sum, ace) { return ace && sum + 10 <= 21 ? sum + 10 : sum; }
    function isSoft(sum, ace) { return ace && sum + 10 <= 21; }

    // ---------- dealer ----------
    function dealerRec(sum, ace, dk, memo) {
      if (sum > 21) return LEAF[sum === 22 ? 5 : 6];
      const soft = ace && sum + 10 <= 21;
      const tot = soft ? sum + 10 : sum;
      if (tot > 17 || (tot === 17 && !(soft && R.h17))) return LEAF[tot - 17];
      let o = memo.get(dk);
      if (o) return o;
      o = new Float64Array(8);
      for (let c = 1; c <= 10; c++) {
        const p = prob(c);
        if (!p) continue;
        add(c);
        const s = dealerRec(sum + c, ace || c === 1, dk + P32[c], memo);
        del(c);
        for (let i = 0; i < 7; i++) o[i] += p * s[i];
      }
      memo.set(dk, o);
      return o;
    }

    // Returns {d, pbj}. d[0..4] = 17..21, d[5] = bust on 22, d[6] = bust 23+, d[7] = dealer BJ
    // (d[7] is only non-zero when the hole card is not checked).
    function dealerDist() {
      const key = inf ? 0 : rkey;
      const m = dealerMemo[U];
      let r = m.get(key);
      if (r) return r;
      const memo = new Map();
      const o = new Float64Array(8);
      let pbj = 0;
      for (let c = 1; c <= 10; c++) {
        const p = prob(c);
        if (!p) continue;
        if ((U === 1 && c === 10) || (U === 10 && c === 1)) { pbj += p; continue; }
        add(c);
        const s = dealerRec(U + c, U === 1 || c === 1, P32[c], memo);
        del(c);
        for (let i = 0; i < 7; i++) o[i] += p * s[i];
      }
      if (cond) { const k = 1 - pbj; if (k > 0) for (let i = 0; i < 7; i++) o[i] /= k; }
      else o[7] = pbj;
      r = { d: o, pbj };
      m.set(key, r);
      return r;
    }

    // ---------- player ----------
    function standWL(t, n, d) {
      if (R.charlie && n >= R.charlie) return [1 - d[7], d[7]];
      let w = d[6] + (R.dealer22Push ? 0 : d[5]), l = d[7];
      for (let i = 0; i < 5; i++) {
        const dt = 17 + i;
        if (dt < t) w += d[i]; else if (dt > t) l += d[i];
      }
      return [w, l];
    }
    function standEV(sum, ace, n, r, f) {
      const d = dealerDist().d;
      const wl = standWL(bestTotal(sum, ace), n, d);
      return (r + f) * wl[0] - r * wl[1];
    }
    function hitEV(sum, ace, n, pk, r, f) {
      let ev = 0;
      for (let c = 1; c <= 10; c++) {
        const p = prob(c);
        if (!p) continue;
        const ns = sum + c;
        if (ns > 21) { ev -= p * r; continue; }
        add(c);
        ev += p * bestPlay(ns, ace || c === 1, n + 1, pk + P32[c], r, f);
        del(c);
      }
      return ev;
    }
    function doubleEV(sum, ace, n, r2, f2) {
      let ev = 0;
      for (let c = 1; c <= 10; c++) {
        const p = prob(c);
        if (!p) continue;
        const ns = sum + c;
        if (ns > 21) { ev -= p * r2; continue; }
        add(c);
        ev += p * standEV(ns, ace || c === 1, n + 1, r2, f2);
        del(c);
      }
      return ev;
    }
    function bestPlay(sum, ace, n, pk, r, f) {
      const key = (inf ? 0 : rkey) + ':' + pk + ':' + r + ':' + f;
      const m = playerMemo[U];
      let v = m.get(key);
      if (v !== undefined) return v;
      v = standEV(sum, ace, n, r, f);
      const t = bestTotal(sum, ace);
      if (t < 21 && !(R.charlie && n >= R.charlie)) {
        const h = hitEV(sum, ace, n, pk, r, f);
        if (h > v) v = h;
        if (R.doubleAnyCards && n >= 3) {
          const dd = doubleEV(sum, ace, n, r + 1, f);
          if (dd > v) v = dd;
        }
      }
      m.set(key, v);
      return v;
    }

    function doubleAllowed(sum, ace, n) {
      if (n !== 2) return R.doubleAnyCards;
      const t = bestTotal(sum, ace);
      switch (R.doubleRule) {
        case '9-11': return t >= 9 && t <= 11;
        case '10-11': return t === 10 || t === 11;
        case '11': return t === 11;
        default: return t < 21;
      }
    }
    function freeDoubleOK(sum, ace, n) {
      return R.freeDouble && n === 2 && !isSoft(sum, ace) && sum >= 9 && sum <= 11;
    }

    // ---------- splitting ----------
    function postSplitEV(r, x, rr, ff) {
      const sum = r + x, ace = r === 1 || x === 1, pk = P32[r] + P32[x];
      if (R.splitAceTenBJ && ace && sum === 11) {
        const d = dealerDist().d;
        return (rr + ff) * R.bjPay * (1 - d[7]) - rr * d[7];
      }
      let best = standEV(sum, ace, 2, rr, ff);
      if (r === 1 && R.splitAces === 'one') return best;
      if (bestTotal(sum, ace) < 21) {
        const h = hitEV(sum, ace, 2, pk, rr, ff);
        if (h > best) best = h;
        if (R.das && doubleAllowed(sum, ace, 2) && (r !== 1 || R.splitAces === 'hitdouble')) {
          const fd = freeDoubleOK(sum, ace, 2);
          const dd = doubleEV(sum, ace, 2, rr + (fd ? 0 : 1), ff + (fd ? 1 : 0));
          if (dd > best) best = dd;
        }
      }
      return best;
    }

    // Expects both pair cards already removed from the shoe.
    function splitEV(r) {
      const freeNew = R.freeSplit && r !== 10;
      const H = r === 1 && !R.resplitAces ? 2 : R.maxHands;
      const pr = prob(r);
      const nr = [0, 0], rr = [0, 0];
      const stakes = [[1, 0], [0, 1]];
      const nTypes = freeNew ? 2 : 1;
      for (let x = 1; x <= 10; x++) {
        const px = prob(x);
        if (!px) continue;
        add(x);
        for (let t = 0; t < nTypes; t++) {
          const ev = postSplitEV(r, x, stakes[t][0], stakes[t][1]);
          if (x === r) rr[t] = ev; else nr[t] += px * ev;
        }
        del(x);
      }
      for (let t = 0; t < nTypes; t++) if (pr < 1) nr[t] /= 1 - pr;
      const vm = new Map();
      function V(kr, kf, h) {
        if (kr + kf === 0) return 0;
        const key = kr * 10000 + kf * 100 + h;
        let v = vm.get(key);
        if (v !== undefined) return v;
        const t = kr > 0 ? 0 : 1;
        const kr1 = t === 0 ? kr - 1 : kr, kf1 = t === 1 ? kf - 1 : kf;
        v = (1 - pr) * (nr[t] + V(kr1, kf1, h));
        if (pr > 0) {
          if (h < H) v += pr * (freeNew ? V(kr, kf + 1, h + 1) : V(kr + 1, kf, h + 1));
          else v += pr * (rr[t] + V(kr1, kf1, h));
        }
        vm.set(key, v);
        return v;
      }
      return freeNew ? V(1, 1, 2) : V(2, 0, 2);
    }

    // ---------- public: analyze one situation ----------
    function setRemoved(cards, u, extra) {
      for (let c = 1; c <= 10; c++) { rm[c] = 0; }
      rmN = 0; rkey = 0; over = 0;
      if (extra) for (let c = 1; c <= 10; c++) for (let k = 0; k < (extra[c] || 0); k++) add(c);
      add(u);
      for (const c of cards) add(c);
      U = u;
    }

    function analyze(cards, u, extra) {
      setRemoved(cards, u, extra);
      let sum = 0, ace = false;
      for (const c of cards) { sum += c; if (c === 1) ace = true; }
      const n = cards.length;
      const dd = dealerDist();
      const pbj = dd.pbj;
      const out = { pbj, natural: false, total: bestTotal(sum, ace), soft: isSoft(sum, ace), actions: {}, dealer: null };
      const wrap = cond ? (ev) => -pbj + (1 - pbj) * ev : (ev) => ev;
      if (sum > 21) { out.bust = true; return out; }
      if (n === 2 && ace && sum === 11) {
        out.natural = true;
        out.actions.stand = (1 - pbj) * R.bjPay;
        if (u === 1 && R.insurance) out.evenMoney = 1;
      } else {
        out.actions.stand = wrap(standEV(sum, ace, n, 1, 0));
        const t = bestTotal(sum, ace);
        if (t < 21 && !(R.charlie && n >= R.charlie)) {
          out.actions.hit = wrap(hitEV(sum, ace, n, (() => { let k = 0; for (const c of cards) k += P32[c]; return k; })(), 1, 0));
          if (doubleAllowed(sum, ace, n)) {
            const fd = freeDoubleOK(sum, ace, n);
            out.actions.double = wrap(doubleEV(sum, ace, n, fd ? 1 : 2, fd ? 1 : 0));
            out.freeDouble = fd;
          }
        }
        if (n === 2 && cards[0] === cards[1] && R.maxHands >= 2) {
          out.actions.split = wrap(splitEV(cards[0]));
          out.freeSplit = R.freeSplit && cards[0] !== 10;
        }
        if (n === 2 && R.surrender !== 'none') {
          if (R.surrender === 'early') out.actions.surrender = -0.5;
          else out.actions.surrender = cond ? -pbj - 0.5 * (1 - pbj) : -0.5 * (1 - pbj) - pbj;
        }
      }
      if (u === 1 && R.insurance) out.insurance = pbj * R.insurancePay - (1 - pbj);
      // dealer final-total distribution (unconditional), for display
      const d = dd.d, dist = new Float64Array(8);
      const k = cond ? 1 - pbj : 1;
      for (let i = 0; i < 7; i++) dist[i] = d[i] * k;
      dist[7] = pbj;
      out.dealer = Array.from(dist);
      let best = null;
      for (const a in out.actions) if (best === null || out.actions[a] > out.actions[best] + 1e-12) best = a;
      out.best = best;
      return out;
    }

    // ---------- outcome odds (probabilities under a given first action, optimal play after) ----------
    // tot: [16 or less, 17, 18, 19, 20, 21, bust, Charlie]; w/p/l: win, push, lose for this hand,
    // conditioned on the dealer not having blackjack when the dealer peeks.
    function emptyOutcome() { return { tot: new Float64Array(8), w: 0, p: 0, l: 0 }; }
    function addScaled(o, s, k) {
      for (let i = 0; i < 8; i++) o.tot[i] += k * s.tot[i];
      o.w += k * s.w; o.p += k * s.p; o.l += k * s.l;
    }
    function standOutcome(sum, ace, n) {
      const o = emptyOutcome();
      const d = dealerDist().d;
      const t = bestTotal(sum, ace);
      const wl = standWL(t, n, d);
      o.tot[R.charlie && n >= R.charlie ? 7 : t <= 16 ? 0 : t - 16] = 1;
      o.w = wl[0]; o.l = wl[1]; o.p = Math.max(0, 1 - wl[0] - wl[1]);
      return o;
    }
    function policyAfterHit(sum, ace, n, pk, r, f) {
      const t = bestTotal(sum, ace);
      if (t >= 21 || (R.charlie && n >= R.charlie)) return 'stand';
      const s = standEV(sum, ace, n, r, f), h = hitEV(sum, ace, n, pk, r, f);
      let best = h > s ? 'hit' : 'stand', v = Math.max(h, s);
      if (R.doubleAnyCards && n >= 3 && doubleEV(sum, ace, n, r + 1, f) > v) best = 'double';
      return best;
    }
    function outcomeOf(sum, ace, n, pk, r, f, action) {
      if (action === 'stand') return standOutcome(sum, ace, n);
      const o = emptyOutcome();
      for (let c = 1; c <= 10; c++) {
        const p = prob(c);
        if (!p) continue;
        const ns = sum + c;
        if (ns > 21) { o.tot[6] += p; o.l += p; continue; }
        add(c);
        const na = ace || c === 1, npk = pk + P32[c];
        const next = action === 'double' ? 'stand' : policyAfterHit(ns, na, n + 1, npk, r, f);
        addScaled(o, outcomeOf(ns, na, n + 1, npk, r, f, next), p);
        del(c);
      }
      return o;
    }
    function postSplitPolicy(r, x) {
      const sum = r + x, ace = r === 1 || x === 1, pk = P32[r] + P32[x];
      if (r === 1 && R.splitAces === 'one') return 'stand';
      if (bestTotal(sum, ace) >= 21) return 'stand';
      const s = standEV(sum, ace, 2, 1, 0), h = hitEV(sum, ace, 2, pk, 1, 0);
      let best = h > s ? 'hit' : 'stand', v = Math.max(h, s);
      if (R.das && doubleAllowed(sum, ace, 2) && (r !== 1 || R.splitAces === 'hitdouble')) {
        const fd = freeDoubleOK(sum, ace, 2);
        if (doubleEV(sum, ace, 2, fd ? 1 : 2, fd ? 1 : 0) > v) best = 'double';
      }
      return best;
    }

    // Returns {pbj, natural, dealer, actions: {stand|hit|double|split: outcome}}; outcomes are unconditional
    // (dealer blackjack folded into "lose", or "push" for a player blackjack). Split is one hand, no resplit.
    function outcomes(cards, u, extra) {
      const base = analyze(cards, u, extra);
      setRemoved(cards, u, extra);
      let sum = 0, ace = false, pk = 0;
      for (const c of cards) { sum += c; if (c === 1) ace = true; pk += P32[c]; }
      const n = cards.length, pbj = base.pbj;
      const res = { pbj, natural: base.natural, dealer: base.dealer, analysis: base, actions: {} };
      if (base.bust) return res;
      const k = cond ? 1 - pbj : 1;
      function finish(o) {
        o.w *= k; o.p *= k; o.l = o.l * k + (cond ? pbj : 0);
        o.dealerBJ = pbj;
        return o;
      }
      if (base.natural) {
        const o = emptyOutcome(); o.tot[5] = 1; o.w = 1 - pbj; o.p = pbj; o.dealerBJ = pbj;
        res.actions.stand = o;
        return res;
      }
      for (const a of ['stand', 'hit', 'double']) {
        if (base.actions[a] === undefined) continue;
        const o = outcomeOf(sum, ace, n, pk, 1, 0, a);
        res.actions[a] = finish(o);
      }
      if (base.actions.split !== undefined) {
        const r = cards[0];
        setRemoved(cards, u, extra);
        const o = emptyOutcome();
        for (let x = 1; x <= 10; x++) {
          const px = prob(x);
          if (!px) continue;
          add(x);
          if (R.splitAceTenBJ && ((r === 1 && x === 10) || (r === 10 && x === 1))) {
            const d = dealerDist().d; const s = emptyOutcome();
            s.tot[5] = 1; s.w = 1 - d[7]; s.l = d[7];
            addScaled(o, s, px);
          } else {
            const pol = postSplitPolicy(r, x);
            addScaled(o, outcomeOf(r + x, r === 1 || x === 1, 2, P32[r] + P32[x], 1, 0, pol), px);
          }
          del(x);
        }
        res.actions.split = finish(o);
      }
      return res;
    }

    function clear() {
      for (let u = 0; u <= 10; u++) { dealerMemo[u] = new Map(); playerMemo[u] = new Map(); }
    }
    function clearUp(u) { dealerMemo[u] = new Map(); playerMemo[u] = new Map(); }

    // probability of the initial deal (player a, b and upcard u), unordered player cards
    function dealProb(a, b, u) {
      function seq(x, y, z) {
        if (inf) return (base[x] / N) * (base[y] / N) * (base[z] / N);
        const p1 = base[x] / N;
        const p2 = (base[z] - (z === x ? 1 : 0)) / (N - 1);
        const p3 = (base[y] - (y === x ? 1 : 0) - (y === z ? 1 : 0)) / (N - 2);
        return p1 * Math.max(p2, 0) * Math.max(p3, 0);
      }
      return a === b ? seq(a, b, u) : seq(a, b, u) + seq(b, a, u);
    }

    // Generator: analyzes all 55 starting hands against all 10 upcards.
    function* computeAll() {
      const results = {}; // key `${a},${b},${u}`
      let done = 0, edge = 0;
      const total = 550;
      const order = [2, 3, 4, 5, 6, 7, 8, 9, 10, 1];
      for (const u of order) {
        for (let a = 1; a <= 10; a++) {
          for (let b = a; b <= 10; b++) {
            const res = analyze([a, b], u);
            res.w = dealProb(a, b, u);
            results[a + ',' + b + ',' + u] = res;
            edge += res.w * res.actions[res.best];
            done++;
            yield { done, total };
          }
        }
        clearUp(u);
      }
      return { results, ev: edge };
    }

    return { rules: R, analyze, outcomes, computeAll, dealProb, clear, inf, N, base };
  }

  // ---------- strategy table builder ----------
  const ACTION_LETTER = { stand: 'S', hit: 'H', double: 'D', split: 'P', surrender: 'R' };

  function codeFor(acts, allowSplit) {
    const keys = Object.keys(acts).filter((k) => allowSplit || k !== 'split');
    let best = keys[0];
    for (const k of keys) if (acts[k] > acts[best] + 1e-12) best = k;
    if (best === 'double') return (acts.hit !== undefined && acts.hit >= acts.stand) ? 'D' : 'Ds';
    if (best === 'surrender') {
      let second = null;
      for (const k of keys) if (k !== 'surrender' && (second === null || acts[k] > acts[second])) second = k;
      if (second === 'double') second = acts.hit >= acts.stand ? 'hit' : 'stand';
      return 'R' + ACTION_LETTER[second].toLowerCase();
    }
    return ACTION_LETTER[best];
  }

  function buildStrategy(results) {
    const hard = {}, soft = {}, pair = {}, comp = {};
    function bucket(obj, row) { return obj[row] || (obj[row] = {}); }
    for (const key in results) {
      const [a, b, u] = key.split(',').map(Number);
      const r = results[key];
      if (r.natural) continue;
      comp[key] = codeFor(r.actions, true);
      const nonSplit = Object.assign({}, r.actions); delete nonSplit.split;
      let table, row;
      if (a === 1 || b === 1) { table = soft; row = a + b + 10; }
      else { table = hard; row = a + b; }
      const cell = bucket(bucket(table, row), u);
      (cell.items || (cell.items = [])).push({ a, b, w: r.w, acts: nonSplit, code: codeFor(nonSplit, false) });
      if (a === b) {
        const pc = bucket(bucket(pair, a), u);
        pc.items = [{ a, b, w: r.w, acts: r.actions, code: comp[key] }];
      }
    }
    function finalize(table, allowSplit) {
      for (const row in table) for (const u in table[row]) {
        const cell = table[row][u];
        let W = 0;
        const avg = {};
        const common = Object.keys(cell.items[0].acts).filter((k) => cell.items.every((it) => it.acts[k] !== undefined));
        for (const it of cell.items) W += it.w;
        for (const k of common) {
          avg[k] = 0;
          for (const it of cell.items) avg[k] += (W > 0 ? it.w / W : 1 / cell.items.length) * it.acts[k];
        }
        cell.acts = avg;
        cell.code = codeFor(avg, allowSplit);
        cell.mixed = cell.items.some((it) => it.code !== cell.code);
      }
    }
    finalize(hard, false); finalize(soft, false); finalize(pair, true);
    return { hard, soft, pair, comp };
  }

  // ---------- Monte Carlo simulator ----------
  function createSim(rules, strat, seed, engine) {
    const multiCache = new Map();
    const R = Object.assign({}, DEFAULT_RULES, rules);
    const inf = !R.decks;
    const cond = R.holeCard !== 'enhc';
    let s = (seed >>> 0) || 0x9e3779b9;
    function rnd() { // mulberry32
      s = (s + 0x6D2B79F5) >>> 0;
      let t = s;
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    }
    const shoe = [];
    if (!inf) for (let d = 0; d < R.decks; d++) for (let c = 1; c <= 13; c++) for (let k = 0; k < 4; k++) shoe.push(Math.min(c, 10));
    let pos = shoe.length;
    const cut = Math.floor(shoe.length * Math.min(Math.max(R.penetration, 0.2), 0.95));
    function shuffle() {
      for (let i = shoe.length - 1; i > 0; i--) { const j = Math.floor(rnd() * (i + 1)); const t = shoe[i]; shoe[i] = shoe[j]; shoe[j] = t; }
      pos = 0;
    }
    function draw() {
      if (inf) { const c = Math.floor(rnd() * 13) + 1; return c > 10 ? 10 : c; }
      if (pos >= shoe.length) shuffle(); // shoe ran out mid-round: reshuffle (rare, single deck at deep penetration)
      return shoe[pos++];
    }
    function total(cards) { let s = 0, a = false; for (const c of cards) { s += c; if (c === 1) a = true; } return a && s + 10 <= 21 ? [s + 10, true, s] : [s, false, s]; }

    function lookup(cards, u, canSplit) {
      if (cards.length === 2) {
        const a = Math.min(cards[0], cards[1]), b = Math.max(cards[0], cards[1]);
        const code = strat.comp[a + ',' + b + ',' + u];
        if (code) {
          if (code === 'P' || code === 'Rp') return canSplit ? code : (code === 'Rp' ? 'R' + fallbackOfPair(cards, u).toLowerCase() : fallbackOfPair(cards, u));
          if (canSplit || a !== b) return code;
          return fallbackOfPair(cards, u);
        }
      }
      const [t, soft] = total(cards);
      if (t >= 21) return 'S';
      if (engine && cards.length >= 3) {
        const key = cards.slice().sort((x, y) => x - y).join('') + '|' + u;
        let code = multiCache.get(key);
        if (!code) {
          const res = engine.analyze(cards, u);
          code = codeFor(res.actions, false);
          multiCache.set(key, code);
        }
        return code;
      }
      const tab = soft ? strat.soft : strat.hard;
      const row = tab[t];
      if (row && row[u]) return row[u].code;
      if (soft) return t >= 19 ? 'S' : 'H';
      return t >= 17 ? 'S' : t <= 11 ? 'H' : 'S';
    }
    function fallbackOfPair(cards, u) {
      const [t, soft] = total(cards);
      const row = (soft ? strat.soft : strat.hard)[t];
      return row && row[u] ? row[u].code : 'H';
    }
    function doubleAllowed(cards, h) {
      if (cards.length !== 2) return R.doubleAnyCards;
      if (h.split && !R.das) return false;
      if (h.splitAce && R.splitAces !== 'hitdouble') return false;
      const [t] = total(cards);
      switch (R.doubleRule) {
        case '9-11': return t >= 9 && t <= 11;
        case '10-11': return t === 10 || t === 11;
        case '11': return t === 11;
        default: return t < 21;
      }
    }

    const st = { rounds: 0, sum: 0, sumSq: 0, win: 0, push: 0, loss: 0, bj: 0, dealerBj: 0, doubles: 0, splits: 0, surrenders: 0, wager: 0, freeBets: 0 };

    function round() {
      if (!inf && (pos >= cut || shoe.length - pos < 15)) shuffle();
      const p = [draw()], up = draw(); p.push(draw()); const hole = draw();
      const dealerBJ = (up === 1 && hole === 10) || (up === 10 && hole === 1);
      const playerBJ = (p[0] === 1 && p[1] === 10) || (p[0] === 10 && p[1] === 1);
      if (dealerBJ) st.dealerBj++;
      st.wager += 1;
      let first = lookup(p, up, R.maxHands >= 2);
      if (!playerBJ && R.surrender === 'early' && first[0] === 'R') { st.surrenders++; return -0.5; }
      if (cond && dealerBJ) return playerBJ ? 0 : -1;
      if (playerBJ) { st.bj++; return dealerBJ ? 0 : R.bjPay; }
      if (R.surrender === 'late' && first[0] === 'R') { st.surrenders++; return dealerBJ ? -1 : -0.5; }

      const hands = [{ c: p, r: 1, f: 0, split: false, splitAce: false, bust: false }];
      for (let i = 0; i < hands.length; i++) {
        const h = hands[i];
        if (h.c.length === 1) h.c.push(draw());
        for (;;) {
          const [t] = total(h.c);
          if (t > 21) { h.bust = true; break; }
          if (t === 21) break;
          if (R.charlie && h.c.length >= R.charlie) break;
          const pairNow = h.c.length === 2 && h.c[0] === h.c[1];
          const canSplit = pairNow && hands.length < R.maxHands && (h.c[0] !== 1 || !h.split || R.resplitAces);
          if (h.splitAce && R.splitAces === 'one' && !canSplit) break;
          let code = lookup(h.c, up, canSplit);
          if (code[0] === 'R') code = code[1].toUpperCase(); // surrender only on the first two cards
          if (h.splitAce && R.splitAces === 'one' && code !== 'P') break;
          if (code === 'P' && canSplit) {
            const r0 = h.c.pop();
            const free = R.freeSplit && r0 !== 10;
            hands.push({ c: [r0], r: free ? 0 : 1, f: free ? 1 : 0, split: true, splitAce: r0 === 1, bust: false });
            if (free) st.freeBets++; else st.wager += 1;
            st.splits++;
            h.split = true; h.splitAce = r0 === 1;
            h.c.push(draw());
            continue;
          }
          if (code === 'P') code = 'H';
          if (code === 'D' || code === 'Ds') {
            if (doubleAllowed(h.c, h)) {
              const [, softNow, hs] = total(h.c);
              const free = R.freeDouble && h.c.length === 2 && !softNow && hs >= 9 && hs <= 11;
              if (free) { h.f += 1; st.freeBets++; } else { h.r += 1; st.wager += 1; }
              st.doubles++;
              h.c.push(draw());
              if (total(h.c)[0] > 21) h.bust = true;
              break;
            }
            code = code === 'D' ? 'H' : 'S';
          }
          if (code === 'S') break;
          h.c.push(draw());
        }
      }
      let net = 0;
      if (!cond && dealerBJ) { for (const h of hands) net -= h.r; return net; }
      const dc = [up, hole];
      if (hands.some((h) => !h.bust)) {
        for (;;) {
          const [t, soft] = total(dc);
          if (t > 17 || (t === 17 && !(soft && R.h17))) break;
          dc.push(draw());
        }
      }
      const [dt] = total(dc);
      for (const h of hands) {
        const [t] = total(h.c);
        if (h.bust) { net -= h.r; continue; }
        if (R.charlie && h.c.length >= R.charlie) { net += h.r + h.f; continue; }
        if (R.splitAceTenBJ && h.split && h.c.length === 2 && t === 21) { net += (h.r + h.f) * R.bjPay; continue; }
        if (dt > 21) { if (!(R.dealer22Push && dt === 22)) net += h.r + h.f; continue; }
        if (t > dt) net += h.r + h.f; else if (t < dt) net -= h.r;
      }
      return net;
    }

    function run(n) {
      for (let i = 0; i < n; i++) {
        const v = round();
        st.rounds++; st.sum += v; st.sumSq += v * v;
        if (v > 0) st.win++; else if (v < 0) st.loss++; else st.push++;
      }
      return st;
    }
    if (!inf) shuffle();
    return { run, stats: st };
  }

  const api = { createEngine, buildStrategy, createSim, codeFor, DEFAULT_RULES };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else global.BJ = api;
})(typeof window !== 'undefined' ? window : this);
