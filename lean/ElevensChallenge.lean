/-!
# Elevens Solitaire — Challenge File

This file imports only `Elevens.Basic` (which itself imports only Mathlib) and
states the main confluence theorems with `sorry`.

A human reader can audit two things:

1. **Definitions** in `Elevens/Basic.lean` — `GameState`, `RankState`, `rankState`,
   `IsLegal`, `applyMove`, `Winnable`, `WinnableFlip`.  Pure definitions, no proofs,
   imports only Mathlib.

2. **Statements below** — exactly what this project claims to have proved.

`ElevensSolution.lean` proves these theorems by importing the proof modules.
Run `lake env comparator comparator.json` to verify the solution uses only the
standard axioms (propext, Quot.sound, Classical.choice).

**Win-probability theorems** (`elevensWinRate_eq`, `elevensFlipWinRate_eq`) are not
covered here because they use `native_decide`, whose 42-minute native compilation is
incompatible with comparator's sandboxed kernel replay.  Those results are
independently verified by `python/exact.py`.
-/

import Elevens.Basic

open Elevens

/-- **Theorem 3.4.** If two states have equal rank-states, they have equal winnability. -/
theorem elevens_rankState_determines_outcome (s₁ s₂ : GameState)
    (h : rankState s₁ = rankState s₂) :
    Winnable s₁ ↔ Winnable s₂ := by sorry

/-- **Corollary 3.5 (Confluence, base game).** Any two legal moves from the same state
    lead to states with equal winnability.  The game outcome is determined by the
    initial shuffle alone; no player choice can affect whether the game is won or lost. -/
theorem elevens_confluence (s : GameState) (m₁ m₂ : Move)
    (h₁ : IsLegal s m₁) (h₂ : IsLegal s m₂) :
    Winnable (applyMove s m₁) ↔ Winnable (applyMove s m₂) := by sorry

/-- **Theorem 5.1.** The same rank-state equivalence holds for `WinnableFlip`,
    the winnability predicate for the flip variant. -/
theorem elevens_rankState_determines_outcome_flip (s₁ s₂ : GameState)
    (h : rankState s₁ = rankState s₂) :
    WinnableFlip s₁ ↔ WinnableFlip s₂ := by sorry

/-- **Corollary (Confluence, flip variant).** The flip variant is also confluent. -/
theorem elevens_confluenceFlip (s : GameState) (m₁ m₂ : Move)
    (h₁ : IsLegal s m₁) (h₂ : IsLegal s m₂) :
    WinnableFlip (applyMove s m₁) ↔ WinnableFlip (applyMove s m₂) := by sorry
