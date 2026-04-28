import Elevens.Confluence

/-!
# Confluence of Elevens-with-Flip Solitaire

Formalizes the flip-variant confluence proof from
docs/proof/confluence_flip.md.

All theorems are fully proved with no sorry placeholders.
-/

namespace Elevens

/-! ## Flip definitions -/

/-- Given a numeric rank r, find a board slot holding rank (complement r). -/
def flipMatchSlot (s : GameState) (r : NumRank) : Option (Fin 9) :=
  (List.finRange 9).find? (fun i =>
    match s.board i with
    | some c => c.rank == .num (complement r)
    | none   => false)

/-- Apply the flip transition. Returns `none` if flip fails. -/
def applyFlip (s : GameState) : Option GameState :=
  match s.pile with
  | [] => none
  | fc :: rest =>
    match fc.rank with
    | .face _ => none
    | .num r =>
      match flipMatchSlot s r with
      | none   => none
      | some i =>
        let b' := clearSlots s.board {i}
        let (b'', pile'') := refill b' rest
        some { board := b'', pile := pile'' }

/-! ## WinnableFlip -/

/-- Winnability for the flip variant. -/
inductive WinnableFlip : GameState → Prop where
  | win  : IsWin s → WinnableFlip s
  | move : IsLegal s m → WinnableFlip (applyMove s m) → WinnableFlip s
  | flip : IsTerminal s → applyFlip s = some s' → WinnableFlip s' → WinnableFlip s

/-! ## Helper lemmas -/

private lemma remaining_eq_rankState' (s : GameState) :
    remaining s =
    Multiset.card (rankState s).boardRanks + (rankState s).pileRanks.length := by
  simp only [remaining, rankState, List.length_map, Multiset.coe_card]
  rw [← List.map_filterMap, List.length_map]

private lemma isWin_iff_rankState' (s : GameState) :
    IsWin s ↔ (rankState s).boardRanks = ∅ ∧ (rankState s).pileRanks = [] := by
  constructor
  · intro ⟨hboard, hpile⟩
    refine ⟨?_, by simp [rankState, hpile]⟩
    simp only [rankState]
    have : (List.finRange 9).filterMap (fun i => (s.board i).map (·.rank)) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro i _; simp [hboard i]
    simp [this]
  · intro ⟨hbr, hpr⟩
    refine ⟨fun i => ?_, ?_⟩
    · by_contra h
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp h
      have hmem : c.rank ∈ ((rankState s).boardRanks : Multiset Rank) := by
        simp only [rankState, Multiset.mem_coe, List.mem_filterMap]
        exact ⟨i, List.mem_finRange i, by simp [hc]⟩
      simp [hbr] at hmem
    · have : (rankState s).pileRanks = s.pile.map Card.rank := rfl
      rw [this] at hpr
      exact List.map_eq_nil_iff.mp hpr

private lemma mem_boardRanks_iff' (s : GameState) (r : Rank) :
    r ∈ ((rankState s).boardRanks : Multiset Rank) ↔
    ∃ i : Fin 9, ∃ c : Card, s.board i = some c ∧ c.rank = r := by
  simp only [rankState, Multiset.mem_coe, List.mem_filterMap]
  constructor
  · rintro ⟨i, _, h⟩
    rcases hboard : s.board i with _ | c
    · simp [hboard] at h
    · simp only [hboard, Option.map_some] at h
      exact ⟨i, c, hboard, Option.some_inj.mp h⟩
  · rintro ⟨i, c, hc, hr⟩
    exact ⟨i, List.mem_finRange i, by simp [hc, hr]⟩

-- Delegates to the corresponding lemma in Confluence.lean.
private lemma remaining_applyMove_lt' (s : GameState) (m : Move)
    (h : IsLegal s m) : remaining (applyMove s m) < remaining s :=
  remaining_applyMove_lt s m h

/-! ## flipMatchSlot properties -/

/-- If `flipMatchSlot s r = some i`, slot i holds a card of rank `.num (complement r)`. -/
private lemma flipMatchSlot_board (s : GameState) (r : NumRank) (i : Fin 9)
    (h : flipMatchSlot s r = some i) :
    ∃ c : Card, s.board i = some c ∧ c.rank = Rank.num (complement r) := by
  simp only [flipMatchSlot] at h
  -- find?_some: the predicate at i is true
  have hpred : (match s.board i with
      | some c => c.rank == .num (complement r)
      | none   => false) = true :=
    @List.find?_some _ (fun j => match s.board j with
      | some c => c.rank == .num (complement r)
      | none   => false) i (List.finRange 9) h
  rcases hboard : s.board i with _ | c
  · simp [hboard] at hpred
  · simp only [hboard, beq_iff_eq] at hpred
    exact ⟨c, rfl, hpred⟩

private lemma flipMatchSlot_board_ne_none (s : GameState) (r : NumRank) (i : Fin 9)
    (h : flipMatchSlot s r = some i) : s.board i ≠ none := by
  obtain ⟨c, hc, _⟩ := flipMatchSlot_board s r i h
  simp [hc]

/-- `flipMatchSlot s r = none` iff `.num (complement r) ∉ boardRanks s`. -/
private lemma flipMatchSlot_none_iff (s : GameState) (r : NumRank) :
    flipMatchSlot s r = none ↔
    Rank.num (complement r) ∉ ((rankState s).boardRanks : Multiset Rank) := by
  simp only [flipMatchSlot, List.find?_eq_none]
  constructor
  · intro hforall hmem
    rw [mem_boardRanks_iff'] at hmem
    obtain ⟨i, c, hboard, hrank⟩ := hmem
    have hi := hforall i (List.mem_finRange i)
    rw [hboard, ← hrank] at hi
    simp only [beq_self_eq_true] at hi
    exact absurd trivial hi
  · intro hnotmem i _
    rcases hboard : s.board i with _ | c
    · simp
    · simp only [hboard, beq_iff_eq, Bool.not_eq_true]
      intro heq
      exact hnotmem ((mem_boardRanks_iff' s _).mpr ⟨i, c, hboard, heq⟩)

private lemma flipMatchSlot_some_mem (s : GameState) (r : NumRank) (i : Fin 9)
    (h : flipMatchSlot s r = some i) :
    Rank.num (complement r) ∈ ((rankState s).boardRanks : Multiset Rank) := by
  rw [mem_boardRanks_iff']
  obtain ⟨c, hboard, hrank⟩ := flipMatchSlot_board s r i h
  exact ⟨i, c, hboard, hrank⟩

/-! ## remaining decreases under applyFlip -/

private lemma applyFlip_success_iff (s s' : GameState) :
    applyFlip s = some s' ↔
    ∃ (fc : Card) (rest : List Card) (r : NumRank) (slot : Fin 9),
      s.pile = fc :: rest ∧ fc.rank = Rank.num r ∧ flipMatchSlot s r = some slot ∧
      s' = { board := (refill (clearSlots s.board {slot}) rest).1,
             pile  := (refill (clearSlots s.board {slot}) rest).2 } := by
  constructor
  · intro h
    unfold applyFlip at h
    rcases hs_pile : s.pile with _ | ⟨fc, rest⟩
    · simp only [hs_pile] at h
      exact absurd h (by simp)
    · simp only [hs_pile] at h
      rcases hfc : fc.rank with r | fr
      · simp only [hfc] at h
        rcases hmatch : flipMatchSlot s r with _ | slot
        · simp only [hmatch] at h; exact absurd h (by simp)
        · simp only [hmatch] at h
          exact ⟨fc, rest, r, slot, rfl, hfc, hmatch, (Option.some_inj.mp h).symm⟩
      · simp only [hfc] at h; exact absurd h (by simp)
  · rintro ⟨fc, rest, r, slot, hs_pile, hrank, hmatch, rfl⟩
    unfold applyFlip
    simp only [hs_pile, hrank, hmatch]

private lemma remaining_applyFlip_lt (s s' : GameState)
    (h : applyFlip s = some s') : remaining s' < remaining s := by
  rw [applyFlip_success_iff] at h
  obtain ⟨fc, rest, r, slot, hs_pile, _, hmatch, hs'⟩ := h
  -- remaining s' = remaining (refill (clearSlots s.board {slot}) rest)
  have hrem_s' : remaining s' =
      (List.finRange 9 |>.filterMap (refill (clearSlots s.board {slot}) rest).1).length +
      (refill (clearSlots s.board {slot}) rest).2.length := by
    rw [hs']; simp [remaining]
  have hconserve := refill_conserves' (clearSlots s.board {slot}) rest
  have hslot_ne_none : s.board slot ≠ none :=
    flipMatchSlot_board_ne_none s r slot hmatch
  have hocc : ∀ j ∈ ({slot} : Finset (Fin 9)), s.board j ≠ none := fun j hj => by
    simp only [Finset.mem_singleton] at hj
    rw [hj]
    exact hslot_ne_none
  have hclear := clearSlots_occupied_length s.board {slot} hocc
  simp only [Finset.card_singleton] at hclear
  have hrest : rest.length + 1 = s.pile.length := by rw [hs_pile]; simp
  simp only [remaining] at *
  linarith

/-! ## applyFlip preserves rank-state comparability -/

-- Helper: rankState equality implies pileRanks (as List) equality
private lemma pileRanks_eq_of_rankState (s₁ s₂ : GameState)
    (h : rankState s₁ = rankState s₂) :
    s₁.pile.map Card.rank = s₂.pile.map Card.rank :=
  congrArg RankState.pileRanks h

-- Helper: rankState equality for post-flip results when cleared boards and pile tails have
-- equal rank multisets and sequences
private lemma rankState_refill_eq_of_rank_eq (b₁ b₂ : Board) (p₁ p₂ : List Card)
    (hbranks : ((List.finRange 9).filterMap (fun i => (b₁ i).map Card.rank) : Multiset Rank) =
               (List.finRange 9).filterMap (fun i => (b₂ i).map Card.rank))
    (hpranks : p₁.map Card.rank = p₂.map Card.rank) :
    rankState { board := (refill b₁ p₁).1, pile := (refill b₁ p₁).2 } =
    rankState { board := (refill b₂ p₂).1, pile := (refill b₂ p₂).2 } := by
  have hplen : p₁.length = p₂.length := by
    have := congrArg List.length hpranks; simp at this; exact this
  have hempty_eq : (List.finRange 9).countP (fun i => b₁ i = none) =
                   (List.finRange 9).countP (fun i => b₂ i = none) := by
    have h1 := countP_none_add_filterMap_eq_nine b₁
    have h2 := countP_none_add_filterMap_eq_nine b₂
    have hcard : (List.finRange 9 |>.filterMap (fun i => (b₁ i).map Card.rank)).length =
                 (List.finRange 9 |>.filterMap (fun i => (b₂ i).map Card.rank)).length := by
      have := congrArg Multiset.card hbranks
      simp only [Multiset.coe_card] at this; exact this
    simp only [← List.map_filterMap, List.length_map] at hcard
    omega
  have hpile_out : (refill b₁ p₁).2.map Card.rank = (refill b₂ p₂).2.map Card.rank := by
    rw [refill_pile, refill_pile, hempty_eq, hplen, List.map_drop, List.map_drop, hpranks]
  have htot₁ := refill_rank_total b₁ p₁
  have htot₂ := refill_rank_total b₂ p₂
  have hpout_ms : ((refill b₁ p₁).2.map Card.rank : Multiset Rank) =
                  (refill b₂ p₂).2.map Card.rank :=
    congrArg (↑· : List Rank → Multiset Rank) hpile_out
  have hbout_eq :
      ((List.finRange 9).filterMap (fun i => ((refill b₁ p₁).1 i).map Card.rank) : Multiset Rank) =
      (List.finRange 9).filterMap (fun i => ((refill b₂ p₂).1 i).map Card.rank) := by
    have hpranks_ms : (p₁.map Card.rank : Multiset Rank) = p₂.map Card.rank :=
      congrArg (↑· : List Rank → Multiset Rank) hpranks
    have heq : ((List.finRange 9).filterMap (fun i => ((refill b₁ p₁).1 i).map Card.rank) : Multiset Rank) +
               (refill b₂ p₂).2.map Card.rank =
               (List.finRange 9).filterMap (fun i => ((refill b₂ p₂).1 i).map Card.rank) +
               (refill b₂ p₂).2.map Card.rank := by
      calc ((List.finRange 9).filterMap (fun i => ((refill b₁ p₁).1 i).map Card.rank) : Multiset Rank) +
           (refill b₂ p₂).2.map Card.rank
          = ((List.finRange 9).filterMap (fun i => ((refill b₁ p₁).1 i).map Card.rank) : Multiset Rank) +
            (refill b₁ p₁).2.map Card.rank := by rw [hpout_ms]
        _ = (List.finRange 9).filterMap (fun i => (b₁ i).map Card.rank) +
            p₁.map Card.rank := htot₁
        _ = (List.finRange 9).filterMap (fun i => (b₂ i).map Card.rank) +
            p₂.map Card.rank := by rw [hbranks, hpranks_ms]
        _ = ((List.finRange 9).filterMap (fun i => ((refill b₂ p₂).1 i).map Card.rank) : Multiset Rank) +
            (refill b₂ p₂).2.map Card.rank := htot₂.symm
    exact Multiset.add_left_inj.mp heq
  -- RankState is a structure: equal iff fields equal
  have hbr_eq : (rankState { board := (refill b₁ p₁).1, pile := (refill b₁ p₁).2 }).boardRanks =
                (rankState { board := (refill b₂ p₂).1, pile := (refill b₂ p₂).2 }).boardRanks := by
    simp only [rankState]; exact hbout_eq
  have hpr_eq : (rankState { board := (refill b₁ p₁).1, pile := (refill b₁ p₁).2 }).pileRanks =
                (rankState { board := (refill b₂ p₂).1, pile := (refill b₂ p₂).2 }).pileRanks := by
    simp only [rankState]; exact hpile_out
  cases hrk₁ : rankState { board := (refill b₁ p₁).1, pile := (refill b₁ p₁).2 }
  cases hrk₂ : rankState { board := (refill b₂ p₂).1, pile := (refill b₂ p₂).2 }
  simp only [hrk₁, hrk₂] at hbr_eq hpr_eq
  simp only [hrk₁, hrk₂, hbr_eq, hpr_eq]

private lemma applyFlip_rankState_iff (s₁ s₂ : GameState)
    (hrk : rankState s₁ = rankState s₂) :
    (applyFlip s₁ = none ↔ applyFlip s₂ = none) ∧
    ∀ t₁, applyFlip s₁ = some t₁ →
    ∃ t₂, applyFlip s₂ = some t₂ ∧ rankState t₁ = rankState t₂ := by
  have hpr : s₁.pile.map Card.rank = s₂.pile.map Card.rank :=
    pileRanks_eq_of_rankState s₁ s₂ hrk
  have hbr : (rankState s₁).boardRanks = (rankState s₂).boardRanks :=
    congrArg RankState.boardRanks hrk
  -- Helper: extract pile head rank info from pileRanks equality
  have pile_info : ∀ (sa sb : GameState) (fca : Card) (resta : List Card),
      sa.pile = fca :: resta → sa.pile.map Card.rank = sb.pile.map Card.rank →
      ∃ fcb restb, sb.pile = fcb :: restb ∧ fcb.rank = fca.rank ∧
        resta.map Card.rank = restb.map Card.rank := by
    intro sa sb fca resta hsa hpab
    have hlen : sb.pile.length = (fca :: resta).length := by
      rw [← hsa]; have := congrArg List.length hpab; simp at this; omega
    rcases hs₂ : sb.pile with _ | ⟨fcb, restb⟩
    · simp [hs₂, List.length_cons] at hlen
    · have hpab' := hpab; rw [hsa, hs₂] at hpab'
      simp only [List.map_cons, List.cons.injEq] at hpab'
      obtain ⟨hhead, htail⟩ := hpab'
      exact ⟨fcb, restb, rfl, hhead.symm, htail⟩
  -- Helper: if boardRanks are equal and flipMatchSlot found a match in sa, it finds one in sb
  have flip_match : ∀ (sa sb : GameState) (r : NumRank) (slota : Fin 9),
      (rankState sa).boardRanks = (rankState sb).boardRanks →
      flipMatchSlot sa r = some slota →
      ∃ slotb, flipMatchSlot sb r = some slotb := by
    intro sa sb r slota hbr_ab hmatch_a
    have hmem : Rank.num (complement r) ∈ ((rankState sb).boardRanks : Multiset Rank) := by
      rw [← hbr_ab]; exact flipMatchSlot_some_mem sa r slota hmatch_a
    rcases hm : flipMatchSlot sb r with _ | slotb
    · rw [flipMatchSlot_none_iff] at hm; exact absurd hmem hm
    · exact ⟨slotb, rfl⟩
  -- Helper: cleared board rank multisets are equal when both remove .num (complement r)
  have clear_ranks_eq : ∀ (sa sb : GameState) (r : NumRank) (slota slotb : Fin 9),
      ((List.finRange 9).filterMap (fun i => (sa.board i).map Card.rank) : Multiset Rank) =
      (List.finRange 9).filterMap (fun i => (sb.board i).map Card.rank) →
      flipMatchSlot sa r = some slota → flipMatchSlot sb r = some slotb →
      ((List.finRange 9).filterMap (fun i => (clearSlots sa.board {slota} i).map Card.rank) : Multiset Rank) =
      (List.finRange 9).filterMap (fun i => (clearSlots sb.board {slotb} i).map Card.rank) := by
    intro sa sb r slota slotb hbranks_ab hmatch_a hmatch_b
    have hclear_a := clearSlots_filterMap_rank_add sa.board {slota}
    have hclear_b := clearSlots_filterMap_rank_add sb.board {slotb}
    have hslot_rank : ∀ (sx : GameState) (slotx : Fin 9),
        flipMatchSlot sx r = some slotx →
        ({slotx} : Finset (Fin 9)).val.filterMap (fun i => (sx.board i).map Card.rank) =
        {Rank.num (complement r)} := by
      intro sx slotx hmatch_x
      obtain ⟨c, hc, hcrank⟩ := flipMatchSlot_board sx r slotx hmatch_x
      have hmap : (sx.board slotx).map Card.rank = some (Rank.num (complement r)) := by
        simp [hc, hcrank]
      simp only [Finset.singleton_val, ← Multiset.cons_zero]
      have hf : (fun i => Option.map Card.rank (sx.board i)) slotx = some (Rank.num (complement r)) := hmap
      calc Multiset.filterMap (fun i => Option.map Card.rank (sx.board i)) (slotx ::ₘ 0)
          = (Rank.num (complement r)) ::ₘ Multiset.filterMap (fun i => Option.map Card.rank (sx.board i)) 0 :=
            Multiset.filterMap_cons_some _ _ _ hf
        _ = {Rank.num (complement r)} := by simp [Multiset.filterMap_zero, Multiset.cons_zero]
    have hslot_a_rank := hslot_rank sa slota hmatch_a
    have hslot_b_rank := hslot_rank sb slotb hmatch_b
    rw [hslot_a_rank] at hclear_a
    rw [hslot_b_rank] at hclear_b
    exact Multiset.add_left_inj.mp (by rw [hclear_a, hclear_b, hbranks_ab])
  -- Main proof
  constructor
  · -- none ↔ none: use contrapositive (success in s₁ ↔ success in s₂)
    constructor
    · -- applyFlip s₁ = none → applyFlip s₂ = none
      -- contrapositive: applyFlip s₂ = some t₂ → applyFlip s₁ = some t₁
      intro h₁
      by_contra h₂_ne
      obtain ⟨t₂, ht₂⟩ := Option.ne_none_iff_exists'.mp (by simpa using h₂_ne)
      rw [applyFlip_success_iff] at ht₂
      obtain ⟨fc₂, rest₂, r, slot₂, hs₂, hrank₂, hmatch₂, _⟩ := ht₂
      obtain ⟨fc₁, rest₁, hs₁, hrank₁, _⟩ := pile_info s₂ s₁ fc₂ rest₂ hs₂ hpr.symm
      have hrank₁' : fc₁.rank = Rank.num r := hrank₁.symm ▸ hrank₂
      obtain ⟨slot₁, hmatch₁⟩ := flip_match s₂ s₁ r slot₂ hbr.symm hmatch₂
      have : applyFlip s₁ = some _ :=
        (applyFlip_success_iff s₁ _).mpr ⟨fc₁, rest₁, r, slot₁, hs₁, hrank₁', hmatch₁, rfl⟩
      rw [h₁] at this; exact absurd this (by simp)
    · -- applyFlip s₂ = none → applyFlip s₁ = none
      intro h₂
      by_contra h₁_ne
      obtain ⟨t₁, ht₁⟩ := Option.ne_none_iff_exists'.mp (by simpa using h₁_ne)
      rw [applyFlip_success_iff] at ht₁
      obtain ⟨fc₁, rest₁, r, slot₁, hs₁, hrank₁, hmatch₁, _⟩ := ht₁
      obtain ⟨fc₂, rest₂, hs₂, hrank₂, _⟩ := pile_info s₁ s₂ fc₁ rest₁ hs₁ hpr
      have hrank₂' : fc₂.rank = Rank.num r := hrank₂.symm ▸ hrank₁
      obtain ⟨slot₂, hmatch₂⟩ := flip_match s₁ s₂ r slot₁ hbr hmatch₁
      have : applyFlip s₂ = some _ :=
        (applyFlip_success_iff s₂ _).mpr ⟨fc₂, rest₂, r, slot₂, hs₂, hrank₂', hmatch₂, rfl⟩
      rw [h₂] at this; exact absurd this (by simp)
  · -- some direction
    intro t₁ ht₁
    rw [applyFlip_success_iff] at ht₁
    obtain ⟨fc₁, rest₁, r, slot₁, hs₁_pile, hrank₁, hmatch₁, ht₁_def⟩ := ht₁
    obtain ⟨fc₂, rest₂, hs₂_pile, hrank₂, hrest_eq⟩ := pile_info s₁ s₂ fc₁ rest₁ hs₁_pile hpr
    have hrank₂' : fc₂.rank = Rank.num r := hrank₂.symm ▸ hrank₁
    obtain ⟨slot₂, hmatch₂⟩ := flip_match s₁ s₂ r slot₁ hbr hmatch₁
    -- s₂ flip result
    have ht₂ := (applyFlip_success_iff s₂ _).mpr
      ⟨fc₂, rest₂, r, slot₂, hs₂_pile, hrank₂', hmatch₂, rfl⟩
    refine ⟨{ board := (refill (clearSlots s₂.board {slot₂}) rest₂).1,
               pile  := (refill (clearSlots s₂.board {slot₂}) rest₂).2 }, ht₂, ?_⟩
    -- rankState equality
    rw [ht₁_def]
    apply rankState_refill_eq_of_rank_eq
    · -- board rank multisets after clearing equal
      simp only [rankState] at hbr
      exact clear_ranks_eq s₁ s₂ r slot₁ slot₂ hbr hmatch₁ hmatch₂
    · -- pile tail rank sequences equal
      exact hrest_eq

/-! ## exists_rank_twin (local re-proof) -/

-- Given rankState s₁ = rankState s₂ and a legal move m for s₁, finds a legal
-- move m' for s₂ with the same rank effect. Both board rank multisets are equal,
-- so any legal move type (pair r + complement r, or JQK triple) in s₁ finds
-- the same ranks in s₂'s board.
private lemma exists_rank_twin' (s₁ s₂ : GameState) (m : Move)
    (hrk : rankState s₁ = rankState s₂)
    (hm : IsLegal s₁ m) :
    ∃ m' : Move, IsLegal s₂ m' ∧
      rankState (applyMove s₁ m) = rankState (applyMove s₂ m') :=
  exists_rank_twin s₁ s₂ m hrk hm

/-! ## Lemma 1 extension -/

/-- **Lemma 1 (extended).** Two states with equal rank-states are equally
    winnable in the flip variant.

    Proof by strong induction on `remaining`. Three transition cases:
    - Case A (regular moves): `exists_rank_twin'` finds a rank-twin move
      for s₂; IH gives equal winnability of successors.
    - Case B (flip): `applyFlip_rankState_iff` gives a corresponding flip
      in s₂ with equal post-flip rank-state; IH gives equal winnability.
    - Case C: impossible — move availability depends only on boardRanks.

    See docs/proof/confluence_flip.md §3. -/
theorem rankState_determines_outcome_flip (s₁ s₂ : GameState)
    (h : rankState s₁ = rankState s₂) :
    WinnableFlip s₁ ↔ WinnableFlip s₂ := by
  induction hn : remaining s₁ using Nat.strongRecOn generalizing s₁ s₂ with
  | ind n ih =>
  have hrem_eq : remaining s₁ = remaining s₂ := by
    rw [remaining_eq_rankState', remaining_eq_rankState', h]
  constructor
  · intro hw₁
    -- Decompose the WinnableFlip proof without a new induction
    -- (rcases preserves s₁ in context)
    rcases hw₁ with hwin | ⟨hleg, hwin_next⟩ | ⟨hterm, hflip, hwin_next⟩
    · -- Base case: s₁ is a win → s₂ is also a win (same rank-state)
      apply WinnableFlip.win
      rwa [isWin_iff_rankState', ← h, ← isWin_iff_rankState']
    · -- Case A: s₁ has a regular move m (implicit); find rank-twin m' for s₂
      -- hleg : IsLegal s₁ ?m, hwin_next : WinnableFlip (applyMove s₁ ?m)
      obtain ⟨m', hm'_legal, hrk_eq⟩ := exists_rank_twin' s₁ s₂ _ h hleg
      apply WinnableFlip.move hm'_legal
      have hrem_lt : remaining (applyMove s₁ _) < n :=
        hn ▸ remaining_applyMove_lt' s₁ _ hleg
      exact (ih _ hrem_lt _ _ hrk_eq rfl).mp hwin_next
    · -- Case B: s₁ flip triggered; find corresponding flip in s₂
      -- hterm : IsTerminal s₁, hflip : applyFlip s₁ = some ?s', hwin_next : WinnableFlip ?s'
      obtain ⟨t₂, hflip₂, hrk_eq⟩ := (applyFlip_rankState_iff s₁ s₂ h).2 _ hflip
      have hterm₂ : IsTerminal s₂ := fun m hm => by
        obtain ⟨m', hm', _⟩ := exists_rank_twin' s₂ s₁ m h.symm hm
        exact hterm m' hm'
      apply WinnableFlip.flip hterm₂ hflip₂
      have hrem_lt : remaining _ < n := hn ▸ remaining_applyFlip_lt s₁ _ hflip
      exact (ih _ hrem_lt _ _ hrk_eq rfl).mp hwin_next
  · intro hw₂
    rcases hw₂ with hwin | ⟨hleg, hwin_next⟩ | ⟨hterm, hflip, hwin_next⟩
    · apply WinnableFlip.win
      rwa [isWin_iff_rankState', h, ← isWin_iff_rankState']
    · rename_i m_orig
      obtain ⟨m', hm'_legal, hrk_eq⟩ := exists_rank_twin' s₂ s₁ m_orig h.symm hleg
      apply WinnableFlip.move hm'_legal
      have hrem_s₂ : remaining s₂ = n := hrem_eq ▸ hn
      have hrem_lt : remaining (applyMove s₂ m_orig) < n :=
        hrem_s₂ ▸ remaining_applyMove_lt' s₂ m_orig hleg
      have hrem_lt' : remaining (applyMove s₁ m') < n := by
        have heq : remaining (applyMove s₁ m') = remaining (applyMove s₂ m_orig) := by
          simp only [remaining_eq_rankState', hrk_eq.symm]
        omega
      exact (ih _ hrem_lt' (applyMove s₁ m') (applyMove s₂ m_orig) hrk_eq.symm rfl).mpr hwin_next
    · obtain ⟨t₁, hflip₁, hrk_eq⟩ := (applyFlip_rankState_iff s₂ s₁ h.symm).2 _ hflip
      have hterm₁ : IsTerminal s₁ := fun m hm => by
        obtain ⟨m', hm', _⟩ := exists_rank_twin' s₁ s₂ m h hm
        exact hterm m' hm'
      apply WinnableFlip.flip hterm₁ hflip₁
      have hrem_s₂ : remaining s₂ = n := hrem_eq ▸ hn
      rename_i s'_orig
      have hrem_lt : remaining s'_orig < n :=
        hrem_s₂ ▸ remaining_applyFlip_lt s₂ s'_orig hflip
      have hrem_lt' : remaining t₁ < n := by
        have heq : remaining t₁ = remaining s'_orig := by
          simp only [remaining_eq_rankState', hrk_eq.symm]
        omega
      exact (ih _ hrem_lt' t₁ _ hrk_eq.symm rfl).mpr hwin_next

/-! ## Helper for confluenceFlip: forward direction -/

-- Flip analogue of the forward direction of outcome_deterministic from Confluence.lean.
-- Argument by strong induction on remaining s:
-- Given WinnableFlip (applyMove s m₁) and IsLegal s m₂, produces
-- WinnableFlip (applyMove s m₂).
--
-- If m₁ and m₂ are disjoint: by disjoint_moves_commute (Lemma 2),
--   apply m₂ then m₁ gives same rank-state as m₁ then m₂.
--   WinnableFlip (applyMove s m₁) → WinnableFlip (applyMove (applyMove s m₁) m₂)
--   by the IH applied to (applyMove s m₁, m₂). Then rank-equality of
--   T₁ and T₂ gives WinnableFlip T₂. Then IH on (applyMove s m₂) completes.
-- If m₁ and m₂ share a slot: by shared_slot_rank_preserved (Lemma 3),
--   rankState (applyMove s m₁) = rankState (applyMove s m₂), and
--   rankState_determines_outcome_flip gives the result directly.
private lemma winnableFlip_fwd (s : GameState) (m₁ : Move) (h₁ : IsLegal s m₁)
    (hw : WinnableFlip (applyMove s m₁)) (m₂ : Move) (h₂ : IsLegal s m₂) :
    WinnableFlip (applyMove s m₂) := by
  induction hn : remaining s using Nat.strongRecOn generalizing s m₁ m₂ with
  | ind n ih =>
  by_cases hdisj : Disjoint m₁ m₂
  · -- Disjoint case: use disjoint commutativity
    set T₁ := applyMove s m₁
    set T₂ := applyMove s m₂
    -- m₂ is still legal in T₁ (disjoint moves preserve legality)
    have hm₂_T₁ : IsLegal T₁ m₂ :=
      disjoint_preserves_legality s m₁ m₂ h₁ h₂ hdisj
    -- m₁ is still legal in T₂ (symmetric)
    have hm₁_T₂ : IsLegal T₂ m₁ :=
      disjoint_preserves_legality s m₂ m₁ h₂ h₁ (Disjoint.symm hdisj)
    -- T₁ has strictly smaller remaining than s
    have hrem_T₁ : remaining T₁ < n :=
      hn ▸ remaining_applyMove_lt s m₁ h₁
    -- rcases on hw — rule out .win and .flip, only .move is possible
    rcases hw with hwin | ⟨hleg_m3, hwin_m3⟩ | ⟨hterm, _, _⟩
    · -- .win case: IsWin T₁ but m₂ is legal in T₁ — contradiction
      have hslots : ∀ i ∈ m₂, T₁.board i ≠ none :=
        legal_slots_occupied' T₁ m₂ hm₂_T₁
      have hpos : 0 < m₂.card := legal_move_card_pos' s m₂ h₂
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      exact absurd (hwin.1 i) (hslots i hi)
    · -- .move case: m3 legal at T₁, WinnableFlip (applyMove T₁ m3)
      -- By IH at T₁: WinnableFlip (applyMove T₁ m₂)
      have hwin_T₁m₂ : WinnableFlip (applyMove T₁ m₂) :=
        ih (remaining T₁) hrem_T₁ T₁ _ hleg_m3 hwin_m3 _ hm₂_T₁ rfl
      -- applyMove T₁ m₂ and applyMove T₂ m₁ have equal rank-states
      have hcomm : rankState (applyMove T₁ m₂) = rankState (applyMove T₂ m₁) :=
        disjoint_moves_commute s m₁ m₂ h₁ h₂ hdisj
      -- So WinnableFlip (applyMove T₂ m₁)
      have hwin_T₂m₁ : WinnableFlip (applyMove T₂ m₁) :=
        (rankState_determines_outcome_flip _ _ hcomm).mp hwin_T₁m₂
      -- WinnableFlip T₂ by .move constructor
      exact WinnableFlip.move hm₁_T₂ hwin_T₂m₁
    · -- .flip case: IsTerminal T₁ but m₂ is legal in T₁ — contradiction
      exact absurd hm₂_T₁ (hterm m₂)
  · -- Shared slot case: rankState T₁ = rankState T₂ directly
    exact (rankState_determines_outcome_flip _ _
      (shared_slot_rank_preserved s m₁ m₂ h₁ h₂ hdisj)).mp hw

/-! ## Main Theorems -/

/-- **Theorem (Confluence, Flip Variant).**
    Any two legal regular moves from the same state lead to equally-winnable
    successors in the flip variant.

    See docs/proof/confluence_flip.md §4. -/
theorem confluenceFlip (s : GameState) (m₁ m₂ : Move)
    (h₁ : IsLegal s m₁) (h₂ : IsLegal s m₂) :
    WinnableFlip (applyMove s m₁) ↔ WinnableFlip (applyMove s m₂) :=
  ⟨fun hw => winnableFlip_fwd s m₁ h₁ hw m₂ h₂,
   fun hw => winnableFlip_fwd s m₂ h₂ hw m₁ h₁⟩

/-- **Corollary.** Win rate is well-defined for the flip variant. -/
theorem win_rate_flip_well_defined :
    ∀ (s₁ s₂ : GameState), rankState s₁ = rankState s₂ →
    (WinnableFlip s₁ ↔ WinnableFlip s₂) :=
  rankState_determines_outcome_flip

end Elevens
