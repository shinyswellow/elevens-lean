import Elevens.Basic

/-!
# Elevens Solitaire — Challenge File

This file imports `Elevens.Basic`, which itself imports only Mathlib and contains
**only definitions** (no tactic proofs, no AI-generated proof code). A human reader
can audit `Elevens/Basic.lean` in full in a few minutes: it is ~200 lines defining
card types, game state, legal moves, and winnability.

The theorem statements below are exactly what this project claims to have proved.
`ElevensSolution.lean` proves them by importing the proof modules.

Run `lake env comparator comparator.json` to verify mechanically that the solution
uses only standard Lean axioms (propext, Quot.sound, Classical.choice).

**Win-probability theorems** are not covered here: they use `native_decide`, whose
42-minute native compilation is incompatible with comparator's sandboxed kernel replay.
Those results are independently verified by `python/exact.py`.
-/

open Elevens

/-- **Theorem 3.4.** Equal rank-states imply equal winnability. -/
theorem elevens_rankState_determines_outcome (s₁ s₂ : GameState)
    (h : rankState s₁ = rankState s₂) :
    Winnable s₁ ↔ Winnable s₂ := by sorry

/-- **Corollary 3.5 (Confluence, base game).** Any two legal moves from the same
    state lead to equally winnable successor states. The outcome is determined by
    the initial shuffle alone. -/
theorem elevens_confluence (s : GameState) (m₁ m₂ : Move)
    (h₁ : IsLegal s m₁) (h₂ : IsLegal s m₂) :
    Winnable (applyMove s m₁) ↔ Winnable (applyMove s m₂) := by sorry

/-- **Theorem 5.1.** The same rank-state equivalence holds for `WinnableFlip`. -/
theorem elevens_rankState_determines_outcome_flip (s₁ s₂ : GameState)
    (h : rankState s₁ = rankState s₂) :
    WinnableFlip s₁ ↔ WinnableFlip s₂ := by sorry

/-- **Corollary (Confluence, flip variant).** The flip variant is also confluent. -/
theorem elevens_confluenceFlip (s : GameState) (m₁ m₂ : Move)
    (h₁ : IsLegal s m₁) (h₂ : IsLegal s m₂) :
    WinnableFlip (applyMove s m₁) ↔ WinnableFlip (applyMove s m₂) := by sorry
