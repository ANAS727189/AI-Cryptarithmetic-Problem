# AI Cryptarithmetic Problem

AI-Cryptarithmetic-Problem is a collection of implementations and experiments for solving cryptarithmetic (alphametic) puzzles using algorithmic and AI-oriented approaches. The repository contains JavaScript and C++ solver implementations, small demo UI assets, and examples to help explore search, constraint solving, and heuristics.

## Highlights
- Implementations in JavaScript (for clarity and browser demos) and C++ (for performance experiments).
- Simple web UI to try example puzzles in the browser.
- Focus on clear CSP/backtracking implementations and room to add SAT/SMT encodings or more advanced AI heuristics.

## Languages
- JavaScript — browser demos, CLI scripts and utilities.
- C++ — command-line solvers and performance experiments.
- HTML / CSS — minimal demo pages and styling.

## Getting started

Input format
- Use alphametic notation: words with letters, plus signs (+) and equals (=).
- Example: `SEND + MORE = MONEY`
- Letters are typically uppercase; words can be separated by spaces or plus signs.
- Leading letters of words cannot map to 0.

Algorithm overview
- Backtracking search with constraints:
  - Each unique letter maps to a distinct digit 0–9.
  - Enforce leading-letter ≠ 0.
  - Use column-wise arithmetic constraints and carry propagation to prune search.
- Heuristics (where implemented):
  - Variable ordering (e.g., most constrained / highest degree).
  - Constraint propagation to shrink domains early.
  - Early detection of impossible partial sums.
- Implementations:
  - JavaScript: clarity and demo-friendliness.
  - C++: optimized for speed and larger experiments.

Classic example
- Puzzle: SEND + MORE = MONEY
- Known solution (one mapping): S=9, E=5, N=6, D=7, M=1, O=0, R=8, Y=2
  - That gives 9567 + 1085 = 10652
