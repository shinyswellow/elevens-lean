# Lean 4 Formalization of Elevens Solitaire

Lean 4 formalization accompanying the paper "Confluence and Exact Win Probabilities for Elevens Solitaire." All theorems are fully proved with no `sorry` placeholders.

## Verification notes

The two `native_decide` proofs in `WinProbFull.lean` (standard game and flip variant) each take approximately 42 minutes to verify. Both run sequentially, totalling roughly 84 minutes for a full build. To check that the Lean files compile without running `native_decide` to completion, comment out the `native_decide` lines and replace with `sorry`.

## Setup

Install elan (the Lean version manager):

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Then in this directory:

```bash
lake update    # downloads Mathlib (~20 min first time)
lake build     # compiles the project (~84 min for native_decide proofs)
```

The VS Code Lean 4 extension (`leanprover.lean4`) shows proof state inline.

## File structure

- `lakefile.lean` — project configuration, Mathlib dependency
- `lean-toolchain` — pins the Lean 4 version
- `Elevens.lean` — root import (imports all four modules below)
- `Elevens/Basic.lean` — card types, `GameState`, `RankState`, legal moves, winnability
- `Elevens/Confluence.lean` — Lemmas 3.1–3.3 and Theorem 3.4 (outcome determinism)
- `Elevens/ConfluenceFlip.lean` — Theorem 5.1 (confluence for the flip variant)
- `Elevens/WinProb.lean` — POC DP spike (6-rank game, `poc_win_prob = 3217/5775`)
- `Elevens/WinProbFull.lean` — Full 13-rank DP with 23,040-fold symmetry; `native_decide` theorems for both variants

## Results

- **P(win, standard)** ≈ 20.20% (exact rational in `WinProbFull.lean`)
- **P(win, flip)** ≈ 19.92% (exact rational in `WinProbFull.lean`)
- Confluence holds for both variants (no player choice affects outcome)
