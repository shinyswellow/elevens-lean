# Elevens Solitaire: Confluence and Exact Win Probabilities

Lean 4 formalization accompanying the paper "Confluence and Exact Win Probabilities for Elevens Solitaire."

## Results

- **Confluence**: the outcome of any Elevens game is determined entirely by the initial shuffle — no player choice affects whether the game is won or lost. Proved for both the standard game and the flip variant.
- **P(win, standard)** ≈ 10.689% (exact rational, machine-checked)
- **P(win, flip)** ≈ 19.923% (exact rational, machine-checked)

## Repository structure

```
lean/          Lean 4 formalization (see lean/README.md for setup)
python/        Python dynamic-programming script (cross-verification)
```

## Lean files

| File | Contents |
|------|----------|
| `lean/Elevens/Basic.lean` | Card types, `GameState`, `RankState`, legal moves, winnability |
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
