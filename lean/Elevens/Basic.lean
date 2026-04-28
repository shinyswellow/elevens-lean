import Mathlib

/-!
# Elevens Solitaire — Types and Definitions

Formalizes the game state, legal moves, and rank-state projection
used in the confluence proof. See the accompanying paper for the
human-readable proof this file formalizes.
-/

namespace Elevens

/-! ## Card representation -/

/-- Numeric card ranks, stored as Fin 10 where value n represents rank n+1.
    So 0 = Ace (value 1), 1 = Two (value 2), ..., 9 = Ten (value 10). -/
abbrev NumRank := Fin 10

/-- The numeric value of a NumRank: n + 1. -/
def numericValue (r : NumRank) : ℕ := r.val + 1

/-- The unique complement of a numeric rank: the rank r' such that
    numericValue r + numericValue r' = 11. -/
def complement (r : NumRank) : NumRank :=
  ⟨9 - r.val, by omega⟩

/-- complement_sum: the values of a rank and its complement always sum to 11. -/
@[simp]
theorem complement_sum (r : NumRank) :
    numericValue r + numericValue (complement r) = 11 := by
  fin_cases r <;> decide

/-- Two numeric ranks form a legal sum-to-11 pair. -/
def isLegalPair (r₁ r₂ : NumRank) : Prop :=
  numericValue r₁ + numericValue r₂ = 11

/-- complement is the unique legal pair partner. -/
theorem legal_pair_iff_complement (r₁ r₂ : NumRank) :
    isLegalPair r₁ r₂ ↔ r₂ = complement r₁ := by
  simp only [isLegalPair, numericValue, complement, Fin.ext_iff]
  omega

/-- Face card ranks. -/
inductive FaceRank : Type where
  | J | Q | K
  deriving DecidableEq, Repr, BEq

/-- A card rank: numeric (Ace–Ten) or face (J/Q/K). -/
inductive Rank : Type where
  | num : NumRank → Rank
  | face : FaceRank → Rank
  deriving DecidableEq, Repr

/-- Card suits (irrelevant to game rules). -/
inductive Suit : Type where
  | S | H | D | C
  deriving DecidableEq, Repr

/-- A playing card. -/
structure Card where
  rank : Rank
  suit : Suit
  deriving DecidableEq, Repr

/-! ## Game state -/

/-- The board: 9 named slots, each optionally holding a card.
    None indicates an empty slot (only possible after deck exhaustion). -/
abbrev Board := Fin 9 → Option Card

/-- A game state consists of the current board and the remaining draw pile. -/
structure GameState where
  board : Board
  pile  : List Card

/-- The number of cards remaining in a state (board + pile). -/
def remaining (s : GameState) : ℕ :=
  (List.finRange 9 |>.filterMap s.board).length + s.pile.length

/-! ## Rank-state projection -/

/-- The rank-state of a game state: the multiset of board ranks and the
    sequence of pile ranks. Suits and board positions are discarded. -/
structure RankState where
  boardRanks : Multiset Rank
  pileRanks  : List Rank
  deriving DecidableEq

/-- Compute the rank-state. -/
def rankState (s : GameState) : RankState where
  boardRanks := (List.finRange 9).filterMap (fun i => (s.board i).map (·.rank))
  pileRanks  := s.pile.map (·.rank)

/-! ## Legal moves -/

/-- A move is a set of board positions. -/
abbrev Move := Finset (Fin 9)

/-- A move is a legal number pair: two positions holding numeric cards whose
    ranks sum to 11. -/
def IsLegalNumMove (s : GameState) (m : Move) : Prop :=
  ∃ (i j : Fin 9) (c₁ c₂ : Card) (r₁ r₂ : NumRank),
    i ≠ j ∧
    m = {i, j} ∧
    s.board i = some c₁ ∧ s.board j = some c₂ ∧
    c₁.rank = Rank.num r₁ ∧ c₂.rank = Rank.num r₂ ∧
    isLegalPair r₁ r₂

/-- A move is a legal face triple: three positions holding one J, one Q, one K. -/
def IsLegalFaceMove (s : GameState) (m : Move) : Prop :=
  ∃ (i j k : Fin 9) (cᵢ cⱼ cₖ : Card),
    i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    m = {i, j, k} ∧
    s.board i = some cᵢ ∧ s.board j = some cⱼ ∧ s.board k = some cₖ ∧
    cᵢ.rank = Rank.face FaceRank.J ∧
    cⱼ.rank = Rank.face FaceRank.Q ∧
    cₖ.rank = Rank.face FaceRank.K

/-- A move is legal if it is a legal number pair or a legal face triple. -/
def IsLegal (s : GameState) (m : Move) : Prop :=
  IsLegalNumMove s m ∨ IsLegalFaceMove s m

/-! ## Applying a move -/

/-- Remove cards at positions in m from the board. -/
def clearSlots (b : Board) (m : Move) : Board :=
  fun i => if i ∈ m then none else b i

/-- Refill empty slots left-to-right from the pile. -/
def refill (b : Board) (pile : List Card) : Board × List Card :=
  (List.finRange 9).foldl
    (fun acc i =>
      match acc.1 i, acc.2 with
      | none, c :: cs => (Function.update acc.1 i (some c), cs)
      | _,    _       => acc)
    (b, pile)

/-- Apply a move: clear positions, then refill from pile. -/
def applyMove (s : GameState) (m : Move) : GameState :=
  let b'           := clearSlots s.board m
  let (b'', pile') := refill b' s.pile
  ⟨b'', pile'⟩

/-! ## Win/loss conditions -/

/-- A state is terminal if no legal move exists. -/
def IsTerminal (s : GameState) : Prop :=
  ∀ m : Move, ¬ IsLegal s m

/-- A state is a win: all board slots empty, pile empty. -/
def IsWin (s : GameState) : Prop :=
  (∀ i : Fin 9, s.board i = none) ∧ s.pile = []

/-- A state is winnable iff there exists a finite sequence of legal moves
    leading from it to a win. Using an explicit sequence avoids well-founded
    recursion, which requires proving termination separately. -/
def Winnable (s : GameState) : Prop :=
  ∃ moves : List Move,
    (∀ i : Fin moves.length,
      IsLegal ((moves.take i.val).foldl applyMove s) (moves.get i)) ∧
    IsWin (moves.foldl applyMove s)

end Elevens
