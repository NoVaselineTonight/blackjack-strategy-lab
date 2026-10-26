# Blackjack Strategy Lab

Exact blackjack strategy and house edge for any table rules, in a single static web page.

Open `index.html` in a browser (or serve the folder with any static server). No build step and no dependencies apart from Google Fonts.

## What it does

- **Strategy chart.** Hard, soft and pair tables for the rules you set. Every starting hand (55 two-card combinations) is solved against every dealer upcard by recursing through every card left in the shoe, for both you and the dealer. Select a cell to see the expected value of every action for each card combination.
- **Hand analyzer.** Any hand, including three or more cards, against any upcard, with cards already seen removed from the shoe. It shows the expected value of each action, the insurance value, a Hi-Lo count, and outcome odds: how often you and the dealer finish on each total or bust, and your win, push and lose chances.
- **Simulator.** Deals real shuffled shoes with a cut card, plays them with the computed strategy, and compares the result with the exact house edge. Runs of up to 100 million rounds.
- **Rule effects.** Changes one rule at a time and recomputes the whole game to show what each rule is worth.
- **Saved rules.** Name and save rule sets in your browser, or move them between devices with a rules code.
- **Shortcuts.** In the analyzer, type card keys (A, 2–9, 0/T/J/Q/K) to build a hand, hold Shift to set the upcard, Backspace removes a card and Esc clears. Arrow keys move around the strategy chart, and "Copy chart as text" gives a plain-text card for printing or pasting.

## Rules you can change

Number of decks (1–8 or infinite) · dealer hits or stands on soft 17 · dealer peeks, or no hole card (lose all or original bet only) · blackjack pays 2:1, 3:2, 7:5, 6:5 or 1:1 · insurance and even money · doubling on any two cards, 9–11, 10–11 or 11 · double after split · double on any number of cards · split to 2–8 hands · resplit aces · hit or double split aces · A+10 after a split pays as blackjack · late or early surrender · 5, 6 or 7-card Charlie · dealer 22 pushes · Free Bet free doubles and free splits.

## Accuracy

Results match published figures, for example 6 decks S17 DAS ≈ 0.40%, 6 decks H17 DAS ≈ 0.62%, 8 decks S17 DAS ≈ 0.43%.

Known approximations:

- Split hands draw from the shoe with only the pair and the upcard removed (the standard approach).
- With a peeking dealer, your draws are not conditioned on the hole card not being a ten or ace.
- The simulator plays split hands and Free Bet free hands from the chart rather than solving each one.

## Files

- `engine.js` — the calculation engine (exact recursion, strategy builder, Monte Carlo simulator). Works in the browser (`window.BJ`) and in Node (`require('./engine.js')`).
- `index.html` — the interface.
