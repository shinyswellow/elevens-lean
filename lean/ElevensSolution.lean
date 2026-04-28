import Elevens.Confluence
import Elevens.ConfluenceFlip

/-!
# Elevens Solitaire — Solution File

Proves the theorems stated in `ElevensChallenge.lean` by importing the proof modules.
Comparator verifies these proofs match the challenge statements exactly and use only
standard Lean axioms.
-/

open Elevens

theorem elevens_rankState_determines_outcome (s₁ s₂ : GameState)
    (h : rankState s₁ = rankState s₂) :
    Winnable s₁ ↔ Winnable s₂ :=
  rankState_determines_outcome s₁ s₂ h

theorem elevens_confluence (s : GameState) (m₁ m₂ : Move)
    (h₁ : IsLegal s m₁) (h₂ : IsLegal s m₂) :
    Winnable (applyMove s m₁) ↔ Winnable (applyMove s m₂) :=
  confluence s m₁ m₂ h₁ h₂

theorem elevens_rankState_determines_outcome_flip (s₁ s₂ : GameState)
    (h : rankState s₁ = rankState s₂) :
    WinnableFlip s₁ ↔ WinnableFlip s₂ :=
  rankState_determines_outcome_flip s₁ s₂ h

theorem elevens_confluenceFlip (s : GameState) (m₁ m₂ : Move)
    (h₁ : IsLegal s m₁) (h₂ : IsLegal s m₂) :
    WinnableFlip (applyMove s m₁) ↔ WinnableFlip (applyMove s m₂) :=
  confluenceFlip s m₁ m₂ h₁ h₂
