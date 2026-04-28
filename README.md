# Elevens Solitaire: Confluence and Exact Win Probabilities

Lean 4 formalization accompanying the paper ["Confluence and Exact Win Probabilities for Elevens Solitaire"](paper.pdf).

## Results

- **Confluence**: the outcome of any Elevens game is determined entirely by the initial shuffle — no player choice affects whether the game is won or lost. Proved for both the standard game and the flip variant.
- **P(win, standard)** ≈ 10.689% (exact rational, machine-checked)
- **P(win, flip)** ≈ 19.923% (exact rational, machine-checked)

## Repository structure

```
lean/          Lean 4 formalization (see lean/README.md for setup)
python/        Python dynamic-programming script (cross-verification)
```

## Verifying the proofs

The confluence proofs are split across two files. `lean/ElevensChallenge.lean` imports
`Elevens/Basic.lean` (type definitions and game rules, ~200 lines) and states the four
main theorems with `sorry`. `lean/ElevensSolution.lean` proves them by importing the
proof modules.

[comparator](https://github.com/leanprover/comparator) can mechanically check that the
solution's proofs match the challenge's theorem statements and use only standard axioms
(propext, Quot.sound, Classical.choice):

```bash
cd lean && lake env comparator comparator.json
# Your solution is okay!
```

The win-probability theorems use `native_decide` and are outside comparator's scope —
its sandboxed kernel replay cannot run a 42-minute native compilation. Those results are
independently verified by `python/exact.py`.

## Lean files

| File | Contents |
|------|----------|
| `lean/Elevens/Basic.lean` | Card types, `GameState`, `RankState`, legal moves, winnability — **audit here first** |
| `lean/ElevensChallenge.lean` | Theorem statements with `sorry` — the comparator challenge |
| `lean/ElevensSolution.lean` | Proofs by delegation to the modules below |
| `lean/Elevens/Confluence.lean` | Lemmas 3.1–3.3 and Theorem 3.4 (outcome determinism) |
| `lean/Elevens/ConfluenceFlip.lean` | Theorem 5.1 (confluence for the flip variant) |
| `lean/Elevens/WinProb.lean` | POC DP spike (6-rank game, `poc_win_prob = 3217/5775`) |
| `lean/Elevens/WinProbFull.lean` | Full 13-rank DP with 23,040-fold symmetry; `native_decide` theorems |

All theorems are fully machine-checked with no `sorry` placeholders.

## Python script

`python/exact.py` implements the rank-multiset dynamic program described in the paper (Equations 1 and 2). It reproduces both exact win probabilities and serves as an independent cross-check of the Lean results. Requires Python 3.9+ with no external dependencies.

```bash
python python/exact.py
```

## Verification notes

The two `native_decide` proofs in `WinProbFull.lean` each take approximately 42 minutes to verify. Both run sequentially, totalling roughly 84 minutes for a full `lake build`. To check that the files compile without running `native_decide` to completion, comment out the `native_decide` lines and replace with `sorry`.

## License

MIT. See [LICENSE](LICENSE).
