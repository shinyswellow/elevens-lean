import Elevens.Basic

/-!
# Confluence of Elevens Solitaire — Main Theorems

Formalizes Lemmas 1–3 and the main Outcome Determinism theorem from
docs/proof/confluence.md.
-/

namespace Elevens

/-! ## Helper lemmas about applyMove and board preservation -/

/-- `refill` doesn't change a slot that's already occupied: if the slot held
    `some c` before refill, it still holds `some c` after. -/
private lemma step_ne (acc : Board × List Card) (j i : Fin 9) (c : Card)
    (h : acc.1 i = some c) (hji : j ≠ i) :
    (match acc.1 j, acc.2 with
      | none, x :: xs => (Function.update acc.1 j (some x), xs)
      | _,    _       => acc).1 i = some c := by
  rcases hj : acc.1 j with _ | cj
  · rcases hp : acc.2 with _ | ⟨x, xs⟩
    · simp only [hj, hp]; exact h
    · simp only [hj, hp]
      exact Function.update_of_ne (Ne.symm hji) (some x) acc.1 ▸ h
  · simp only [hj]; exact h

private lemma step_preserves (acc : Board × List Card) (j i : Fin 9) (c : Card)
    (h : acc.1 i = some c) :
    (match acc.1 j, acc.2 with
      | none, x :: xs => (Function.update acc.1 j (some x), xs)
      | _,    _       => acc).1 i = some c := by
  by_cases hji : j = i
  · subst hji; simp [h]
  · exact step_ne acc j i c h hji

private lemma refill_foldl_stable (slots : List (Fin 9)) :
    ∀ (acc : Board × List Card) (i : Fin 9) (c : Card),
    acc.1 i = some c →
    (slots.foldl (fun a j =>
        match a.1 j, a.2 with
        | none, x :: xs => (Function.update a.1 j (some x), xs)
        | _,    _       => a)
      acc).1 i = some c := by
  induction slots with
  | nil => intro acc i c h; exact h
  | cons j rest ih =>
    intro acc i c h
    simp only [List.foldl_cons]
    exact ih _ i c (step_preserves acc j i c h)

private lemma refill_preserves_some (b : Board) (pile : List Card) (i : Fin 9) (c : Card)
    (h : b i = some c) : (refill b pile).1 i = some c := by
  unfold refill; exact refill_foldl_stable _ _ i c h

private lemma clearSlots_not_mem (b : Board) (m : Move) (i : Fin 9) (h : i ∉ m) :
    clearSlots b m i = b i := by simp [clearSlots, h]

/-- The board of `applyMove s m` is the result of refilling the cleared board. -/
private lemma applyMove_board_eq (s : GameState) (m : Move) :
    (applyMove s m).board = (refill (clearSlots s.board m) s.pile).1 := by
  simp only [applyMove]

/-- The pile of `applyMove s m` is the rest of the pile after refilling. -/
private lemma applyMove_pile_eq (s : GameState) (m : Move) :
    (applyMove s m).pile = (refill (clearSlots s.board m) s.pile).2 := by
  simp only [applyMove]

/-- If slot `i` is not in move `m` and was occupied, it stays occupied after `applyMove`. -/
private lemma applyMove_board_of_some_notin (s : GameState) (m : Move) (i : Fin 9) (c : Card)
    (hnotin : i ∉ m) (hboard : s.board i = some c) :
    (applyMove s m).board i = some c := by
  simp only [applyMove]
  exact refill_preserves_some _ s.pile i c
    (clearSlots_not_mem s.board m i hnotin ▸ hboard)

/-! ## Helper lemmas about rank-state -/

/-- Membership in `boardRanks`: a rank is present iff some board slot holds a card
    with that rank. -/
lemma mem_boardRanks_iff (s : GameState) (r : Rank) :
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

/-- `remaining` equals the cardinality of the rank-state:
    number of board cards + pile length. -/
private lemma remaining_eq_rankState (s : GameState) :
    remaining s = Multiset.card (rankState s).boardRanks + (rankState s).pileRanks.length := by
  simp only [remaining, rankState, List.length_map, Multiset.coe_card]
  rw [← List.map_filterMap, List.length_map]

/-- A state is a win iff its rank-state is the empty board with empty pile. -/
private lemma isWin_iff_rankState (s : GameState) :
    IsWin s ↔ (rankState s).boardRanks = ∅ ∧ (rankState s).pileRanks = [] := by
  constructor
  · intro ⟨hboard, hpile⟩
    exact ⟨by simp [rankState, hboard], by simp [rankState, hpile]⟩
  · intro ⟨hbr, hpr⟩
    refine ⟨fun i => ?_, ?_⟩
    · by_contra h
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp h
      exact absurd ((mem_boardRanks_iff s c.rank).mpr ⟨i, c, hc, rfl⟩) (by simp [hbr])
    · exact List.map_eq_nil_iff.mp (show (rankState s).pileRanks = [] from hpr ▸ rfl)

/-! ## Infrastructure for remaining_applyMove_lt -/

private lemma filterMap_update_length_incr
    (l : List (Fin 9)) (j : Fin 9) (hjl : j ∈ l) (hnd : l.Nodup)
    (b : Board) (x : Card) (h : b j = none) :
    (l.filterMap (Function.update b j (some x))).length = (l.filterMap b).length + 1 := by
  induction l with
  | nil => simp at hjl
  | cons a t ih =>
    rw [List.mem_cons] at hjl
    obtain ⟨ha_notin, hnd_t⟩ := List.nodup_cons.mp hnd
    simp only [List.filterMap_cons]
    rcases hjl with rfl | hjt
    · simp only [Function.update_self, h]
      have heq : t.filterMap (Function.update b j (some x)) = t.filterMap b := by
        apply List.filterMap_congr; intro i hi
        apply Function.update_of_ne
        intro hij; simp only [hij] at hi; exact ha_notin hi
      simp [heq]
    · rw [Function.update_of_ne (by intro hij; simp only [← hij] at hjt; exact ha_notin hjt)]
      cases b a <;> simp [ih hjt hnd_t]

private lemma filterMap_finRange_update_none (b : Board) (j : Fin 9) (x : Card)
    (h : b j = none) :
    (List.finRange 9 |>.filterMap (Function.update b j (some x))).length =
    (List.finRange 9 |>.filterMap b).length + 1 :=
  filterMap_update_length_incr _ j (List.mem_finRange j) (List.nodup_finRange 9) b x h

private lemma filterMap_clearSlot_length (b : Board) (j : Fin 9) (h : b j ≠ none) :
    (List.finRange 9 |>.filterMap (Function.update b j none)).length + 1 =
    (List.finRange 9 |>.filterMap b).length := by
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp h
  have hkey : (List.finRange 9 |>.filterMap
      (Function.update (Function.update b j none) j (some c))).length =
      (List.finRange 9 |>.filterMap (Function.update b j none)).length + 1 :=
    filterMap_finRange_update_none _ j c (by simp [Function.update_self])
  have hsimp : Function.update (Function.update b j none) j (some c) = b := by
    funext i; by_cases hij : i = j
    · subst hij; rw [Function.update_self]; exact hc.symm
    · rw [Function.update_of_ne hij, Function.update_of_ne hij]
  rw [hsimp] at hkey; omega

private def accTotal' (acc : Board × List Card) : ℕ :=
  (List.finRange 9 |>.filterMap acc.1).length + acc.2.length

private lemma refill_step_total (j : Fin 9) (acc : Board × List Card) :
    accTotal' (match acc.1 j, acc.2 with
      | none, c :: cs => (Function.update acc.1 j (some c), cs)
      | _, _ => acc) = accTotal' acc := by
  unfold accTotal'
  rcases hj : acc.1 j with _ | cj
  · rcases hp : acc.2 with _ | ⟨x, xs⟩
    · simp [hj, hp]
    · show (List.finRange 9 |>.filterMap (Function.update acc.1 j (some x))).length + xs.length =
           (List.finRange 9 |>.filterMap acc.1).length + (x :: xs).length
      rw [filterMap_finRange_update_none acc.1 j x hj, List.length_cons]; omega
  · simp [hj]

private lemma refill_foldl_total' (slots : List (Fin 9)) (acc : Board × List Card) :
    accTotal' (slots.foldl (fun a j =>
      match a.1 j, a.2 with
      | none, c :: cs => (Function.update a.1 j (some c), cs)
      | _, _ => a) acc) = accTotal' acc := by
  induction slots generalizing acc with
  | nil => simp
  | cons j rest ih => simp only [List.foldl_cons]; rw [ih]; exact refill_step_total j acc

lemma refill_conserves' (b : Board) (pile : List Card) :
    (List.finRange 9 |>.filterMap (refill b pile).1).length + (refill b pile).2.length =
    (List.finRange 9 |>.filterMap b).length + pile.length := by
  have := refill_foldl_total' (List.finRange 9) (b, pile)
  simp only [accTotal'] at this; unfold refill; simpa using this

private lemma clearSlots_eq_update' (b : Board) (elem : Fin 9) (s : Finset (Fin 9)) :
    clearSlots b (insert elem s) = Function.update (clearSlots b s) elem none := by
  funext i; simp only [clearSlots, Finset.mem_insert]
  by_cases h : i = elem
  · subst h; simp [Function.update_self]
  · rw [Function.update_of_ne h]; simp [clearSlots, h]

private lemma clearSlots_of_not_mem' (b : Board) (s : Finset (Fin 9)) (a : Fin 9)
    (ha : a ∉ s) : clearSlots b s a = b a := by simp only [clearSlots, if_neg ha]

lemma clearSlots_occupied_length (b : Board) (m : Finset (Fin 9))
    (hall : ∀ i ∈ m, b i ≠ none) :
    (List.finRange 9 |>.filterMap (clearSlots b m)).length + m.card =
    (List.finRange 9 |>.filterMap b).length := by
  induction m using Finset.induction with
  | empty => simp [clearSlots]
  | @insert a s' ha ih =>
    have hall_s' := fun i hi => hall i (Finset.mem_insert_of_mem hi)
    have hall_a : b a ≠ none := hall a (Finset.mem_insert_self a s')
    have hclear_a : clearSlots b s' a = b a := clearSlots_of_not_mem' b s' a ha
    have hocc : clearSlots b s' a ≠ none := by rw [hclear_a]; exact hall_a
    rw [clearSlots_eq_update' b a s']
    linarith [filterMap_clearSlot_length (clearSlots b s') a hocc, ih hall_s',
              Finset.card_insert_of_notMem ha]

lemma legal_slots_occupied' (s : GameState) (m : Move) (h : IsLegal s m) :
    ∀ i ∈ m, s.board i ≠ none := by
  rcases h with ⟨i, j, c₁, c₂, r₁, r₂, _, rfl, hbi, hbj, _, _, _⟩ |
                ⟨a, b, c, ca, cb, cc, _, _, _, rfl, hba, hbb, hbc, _, _, _⟩
  · intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [*]
  · intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> simp [*]

lemma legal_move_card_pos' (s : GameState) (m : Move) (h : IsLegal s m) :
    0 < m.card := by
  rcases h with ⟨i, j, _, _, _, _, hij, rfl, _, _, _, _, _⟩ |
                ⟨a, b, c, _, _, _, hab, hac, _, rfl, _, _, _, _, _, _⟩
  · simp [Finset.card_pair hij]
  · simp [Finset.card_insert_of_notMem (show a ∉ ({b, c} : Finset (Fin 9)) by simp [hab, hac])]

/-! ## Sub-lemmas for rank-state computation -/

/-- Helper: updating a slot not in `slots` doesn't change the countP of that predicate
    for elements in `slots`. -/
private lemma countP_update_of_notMem (slots : List (Fin 9)) (j : Fin 9) (hjslots : j ∉ slots)
    (b : Board) (x : Card) :
    slots.countP (fun i => (Function.update b j (some x)) i = none) =
    slots.countP (fun i => b i = none) := by
  apply List.countP_congr
  intro i hi
  have hij : i ≠ j := fun h => hjslots (h ▸ hi)
  simp [Function.update_of_ne hij]

/-- The pile suffix after `refill` drops exactly `min (number of None slots in slots) pile.length`
    cards from the pile, when `slots` is nodup. -/
private lemma refill_foldl_pile (slots : List (Fin 9)) (hnd : slots.Nodup) :
    ∀ (acc : Board × List Card),
    (slots.foldl (fun a j =>
        match a.1 j, a.2 with
        | none, c :: cs => (Function.update a.1 j (some c), cs)
        | _, _ => a) acc).2 =
    acc.2.drop (min (slots.countP (fun i => acc.1 i = none)) acc.2.length) := by
  induction slots with
  | nil => intro acc; simp
  | cons j rest ih =>
    intro acc
    rw [List.nodup_cons] at hnd
    obtain ⟨hjrest, hnd_rest⟩ := hnd
    simp only [List.foldl_cons]
    rcases hj : acc.1 j with _ | cj
    · -- slot j is empty
      rcases hp : acc.2 with _ | ⟨x, xs⟩
      · -- pile is empty: simp reduces step to acc
        simp only [hj, hp]
        rw [ih hnd_rest acc, hp]; simp
      · -- pile nonempty: simp reduces step to (update acc.1 j (some x), xs)
        simp only [hj, hp]
        rw [ih hnd_rest (Function.update acc.1 j (some x), xs)]
        rw [countP_update_of_notMem rest j hjrest acc.1 x]
        simp only [List.countP_cons, hj, List.length_cons]
        simp only [decide_eq_true_eq, eq_self_iff_true, ite_true]
        set k := rest.countP (fun i => acc.1 i = none)
        have hmin : min (k + 1) (xs.length + 1) = 1 + min k xs.length := by omega
        rw [hmin, show 1 + min k xs.length = min k xs.length + 1 from by omega, List.drop_succ_cons]
    · -- slot j is occupied: simp reduces step to acc
      simp only [hj]
      rw [ih hnd_rest acc]
      simp [List.countP_cons, hj]

/-- Corollary: the pile after `refill b pile` is exactly `pile.drop k` where
    `k = min (empty-slot count of b) pile.length`. -/
lemma refill_pile (b : Board) (pile : List Card) :
    (refill b pile).2 = pile.drop (min ((List.finRange 9).countP (fun i => b i = none))
                                       pile.length) := by
  have := refill_foldl_pile (List.finRange 9) (List.nodup_finRange 9) (b, pile)
  unfold refill; simpa using this

/-- Updating a None slot with a card adds that card's rank to the filterMap rank multiset. -/
private lemma filterMap_rank_update_none (l : List (Fin 9)) (j : Fin 9) (hj : j ∈ l)
    (hnd : l.Nodup) (b : Board) (x : Card) (hbj : b j = none) :
    (l.filterMap (fun i => ((Function.update b j (some x)) i).map Card.rank) : Multiset Rank) =
    (l.filterMap (fun i => (b i).map Card.rank) : Multiset Rank) + {x.rank} := by
  induction l with
  | nil => simp at hj
  | cons a t ih =>
    rw [List.mem_cons] at hj
    obtain ⟨ha_notin, hnd_t⟩ := List.nodup_cons.mp hnd
    -- Work in Multiset via the coe
    rcases hj with rfl | hjt
    · -- j = a: the head slot is being updated
      simp only [Function.update_self, hbj, List.filterMap_cons, Option.map_none, Option.map_some]
      -- tail is unchanged by the update (j ∉ t = ha_notin)
      have htail_eq : t.filterMap (fun i => ((Function.update b j (some x)) i).map Card.rank) =
                      t.filterMap (fun i => (b i).map Card.rank) := by
        apply List.filterMap_congr
        intro i hi
        congr 1
        apply Function.update_of_ne
        intro hij; subst hij; exact ha_notin hi
      simp only [htail_eq]
      show (x.rank ::ₘ (↑(List.filterMap (fun i => Option.map Card.rank (b i)) t) : Multiset Rank)) =
           ↑(List.filterMap (fun i => Option.map Card.rank (b i)) t) + {x.rank}
      simp [add_comm]
    · -- j ≠ a: head is unchanged
      have haj : a ≠ j := fun h => ha_notin (h ▸ hjt)
      have ih_t := ih hjt hnd_t
      have hae : (Function.update b j (some x)) a = b a := Function.update_of_ne haj (some x) b
      simp only [List.filterMap_cons, hae]
      rcases hba : b a with _ | ca
      · simp only [Option.map_none]
        exact_mod_cast ih_t
      · simp only [Option.map_some]
        have heq : (↑(ca.rank :: List.filterMap (fun i => Option.map Card.rank (Function.update b j (some x) i)) t) : Multiset Rank) =
               ca.rank ::ₘ ↑(List.filterMap (fun i => Option.map Card.rank (Function.update b j (some x) i)) t) := rfl
        rw [heq, ih_t]
        rfl

/-- The multiset of board-ranks plus pile-ranks is preserved by refill:
    `boardRanks(refill b pile) + pileRanks(refill b pile) =
     boardRanks(b) + pileRanks(pile)` (as Multiset Rank). -/
lemma refill_rank_total (b : Board) (pile : List Card) :
    ((List.finRange 9).filterMap (fun i => ((refill b pile).1 i).map Card.rank) : Multiset Rank) +
    ((refill b pile).2.map Card.rank : Multiset Rank) =
    ((List.finRange 9).filterMap (fun i => (b i).map Card.rank) : Multiset Rank) +
    (pile.map Card.rank : Multiset Rank) := by
  -- Prove the analogous statement for the foldl, then unfold refill
  suffices h : ∀ (slots : List (Fin 9)) (acc : Board × List Card),
      ((List.finRange 9).filterMap (fun i => ((slots.foldl (fun a j =>
          match a.1 j, a.2 with
          | none, c :: cs => (Function.update a.1 j (some c), cs)
          | _, _ => a) acc).1 i).map Card.rank) : Multiset Rank) +
      (((slots.foldl (fun a j =>
          match a.1 j, a.2 with
          | none, c :: cs => (Function.update a.1 j (some c), cs)
          | _, _ => a) acc).2.map Card.rank) : Multiset Rank) =
      ((List.finRange 9).filterMap (fun i => (acc.1 i).map Card.rank) : Multiset Rank) +
      (acc.2.map Card.rank : Multiset Rank) by
    have := h (List.finRange 9) (b, pile)
    unfold refill; simpa using this
  intro slots
  induction slots with
  | nil => intro acc; simp
  | cons j rest ih =>
    intro acc
    simp only [List.foldl_cons]
    rcases hj : acc.1 j with _ | cj
    · rcases hp : acc.2 with _ | ⟨x, xs⟩
      · -- slot empty, pile empty: step is identity
        simp only [hj, hp]
        rw [ih acc]; simp [hp]
      · -- slot empty, pile nonempty: step fills slot
        simp only [hj, hp]
        have ih_eq := ih (Function.update acc.1 j (some x), xs)
        have hboard_update : ((List.finRange 9).filterMap
            (fun i => ((Function.update acc.1 j (some x)) i).map Card.rank) : Multiset Rank) =
            ((List.finRange 9).filterMap (fun i => (acc.1 i).map Card.rank) : Multiset Rank) +
            {x.rank} :=
          filterMap_rank_update_none (List.finRange 9) j (List.mem_finRange j)
            (List.nodup_finRange 9) acc.1 x hj
        rw [ih_eq, hboard_update]
        push_cast; abel
    · -- slot occupied: step is identity
      simp only [hj]
      rw [ih acc]

/-- Clearing a slot that is occupied removes its rank from the filterMap rank multiset. -/
private lemma filterMap_rank_clear_occupied (b : Board) (a : Fin 9) (c : Card)
    (hba : b a = some c) :
    ((List.finRange 9).filterMap (fun i => (Function.update b a none i).map Card.rank)
      : Multiset Rank) + ({c.rank} : Multiset Rank) =
    ((List.finRange 9).filterMap (fun i => (b i).map Card.rank) : Multiset Rank) := by
  -- Let b' = update b a none; then b = update b' a (some c) and b' a = none
  have hb'a : (Function.update b a none) a = none := by simp
  have hupdate_back : Function.update (Function.update b a none) a (some c) = b := by
    funext i; by_cases h : i = a
    · subst h; simp [hba]
    · simp [Function.update_of_ne h]
  have key := filterMap_rank_update_none (List.finRange 9) a (List.mem_finRange a)
    (List.nodup_finRange 9) (Function.update b a none) c hb'a
  rw [hupdate_back] at key
  -- key: filterMap rank b = filterMap rank (update b a none) + {c.rank}
  exact key.symm

/-- Clearing slots removes their occupied ranks from the board rank filterMap multiset. -/
lemma clearSlots_filterMap_rank_add (b : Board) (m : Finset (Fin 9)) :
    ((List.finRange 9).filterMap (fun i => (clearSlots b m i).map Card.rank) : Multiset Rank) +
    (m.val.filterMap (fun i => (b i).map Card.rank) : Multiset Rank) =
    ((List.finRange 9).filterMap (fun i => (b i).map Card.rank) : Multiset Rank) := by
  induction m using Finset.induction with
  | empty => simp [clearSlots]
  | @insert a s ha ih =>
    rw [clearSlots_eq_update' b a s, Finset.insert_val_of_notMem ha]
    -- Goal: board_fm(update (cs b s) a none) + (a ::ₘ s.val).filterMap (b·.rank) = board_fm(b)
    rcases hba : b a with _ | c
    · -- b a = none: clearing a is a no-op
      have hba_map : (b a).map Card.rank = none := by simp [hba]
      rw [Multiset.filterMap_cons_none a s.val hba_map]
      -- update (clearSlots b s) a none = clearSlots b s
      have hcs_a : clearSlots b s a = none := by simp [clearSlots, ha, hba]
      have hupd : Function.update (clearSlots b s) a none = clearSlots b s := by
        funext i; by_cases h : i = a
        · subst h; simp [hcs_a]
        · simp [Function.update_of_ne h]
      rw [hupd]; exact ih
    · -- b a = some c: clearing a removes c.rank
      have hba_map : (b a).map Card.rank = some c.rank := by simp [hba]
      rw [Multiset.filterMap_cons_some _ a s.val hba_map]
      have hcs_a : clearSlots b s a = some c := by simp [clearSlots, ha, hba]
      have hclear := filterMap_rank_clear_occupied (clearSlots b s) a c hcs_a
      -- c.rank ::ₘ X = {c.rank} + X (definitional)
      have hcons : (c.rank ::ₘ (s.val.filterMap (fun i => (b i).map Card.rank) : Multiset Rank)) =
                   {c.rank} + s.val.filterMap (fun i => (b i).map Card.rank) := rfl
      rw [hcons]
      -- Goal: ↑(finRange update fm) + ({c.rank} + s.val.fm) = ↑(finRange b fm)
      calc ((List.finRange 9).filterMap (fun i => (Function.update (clearSlots b s) a none i).map Card.rank) : Multiset Rank) +
              ({c.rank} + s.val.filterMap (fun i => (b i).map Card.rank) : Multiset Rank)
          = (((List.finRange 9).filterMap (fun i => (Function.update (clearSlots b s) a none i).map Card.rank) : Multiset Rank) + {c.rank}) +
            s.val.filterMap (fun i => (b i).map Card.rank) := by abel
        _ = ((List.finRange 9).filterMap (fun i => (clearSlots b s i).map Card.rank) : Multiset Rank) +
            s.val.filterMap (fun i => (b i).map Card.rank) := by rw [hclear]
        _ = ((List.finRange 9).filterMap (fun i => (b i).map Card.rank) : Multiset Rank) := ih

/-- The empty-slot count of `clearSlots b m` equals the original count plus the count of
    occupied slots in m that are being cleared. -/
private lemma clearSlots_empty_count_eq (b : Board) (m₁ m₂ : Finset (Fin 9))
    (hrank : m₁.val.filterMap (fun i => (b i).map Card.rank) =
             m₂.val.filterMap (fun i => (b i).map Card.rank)) :
    (List.finRange 9).countP (fun i => clearSlots b m₁ i = none) =
    (List.finRange 9).countP (fun i => clearSlots b m₂ i = none) := by
  -- Use: emptyCount = 9 - occupiedCount, and occupiedCount = |board_ranks|
  -- board_ranks(clearSlots b m) = board_ranks(b) - m_occ_ranks (from clearSlots_filterMap_rank_add)
  -- |board_ranks(clearSlots b m₁)| = |board_ranks(clearSlots b m₂)| (since |m₁.filterMap| = |m₂.filterMap|)
  have hlen₁ := clearSlots_filterMap_rank_add b m₁
  have hlen₂ := clearSlots_filterMap_rank_add b m₂
  -- From these: |clearSlots_rank_fm m₁| = |clearSlots_rank_fm m₂|
  have hcard : ((List.finRange 9).filterMap
        (fun i => (clearSlots b m₁ i).map Card.rank) : Multiset Rank).card =
      ((List.finRange 9).filterMap
        (fun i => (clearSlots b m₂ i).map Card.rank) : Multiset Rank).card := by
    have h₁ : ((List.finRange 9).filterMap
          (fun i => (clearSlots b m₁ i).map Card.rank) : Multiset Rank).card =
        ((List.finRange 9).filterMap (fun i => (b i).map Card.rank) : Multiset Rank).card -
        (m₁.val.filterMap (fun i => (b i).map Card.rank) : Multiset Rank).card := by
      have := Multiset.card_add ((List.finRange 9).filterMap
            (fun i => (clearSlots b m₁ i).map Card.rank) : Multiset Rank)
          (m₁.val.filterMap (fun i => (b i).map Card.rank) : Multiset Rank)
      rw [hlen₁] at this; omega
    have h₂ : ((List.finRange 9).filterMap
          (fun i => (clearSlots b m₂ i).map Card.rank) : Multiset Rank).card =
        ((List.finRange 9).filterMap (fun i => (b i).map Card.rank) : Multiset Rank).card -
        (m₂.val.filterMap (fun i => (b i).map Card.rank) : Multiset Rank).card := by
      have := Multiset.card_add ((List.finRange 9).filterMap
            (fun i => (clearSlots b m₂ i).map Card.rank) : Multiset Rank)
          (m₂.val.filterMap (fun i => (b i).map Card.rank) : Multiset Rank)
      rw [hlen₂] at this; omega
    rw [h₁, h₂, hrank]
  -- Relate card of rank filterMap to length of board filterMap (they're equal: filterMap rank just maps)
  have hcard_occ : ∀ (m : Finset (Fin 9)),
      ((List.finRange 9).filterMap (fun i => (clearSlots b m i).map Card.rank) : Multiset Rank).card =
      ((List.finRange 9).filterMap (clearSlots b m)).length := by
    intro m
    -- Both equal the number of occupied slots; prove by showing the two filterMaps have equal length
    -- via a helper: ∀ l, (l.filterMap (fun i => (f i).map g)).length = (l.filterMap f).length
    suffices h : ∀ (l : List (Fin 9)),
        (l.filterMap (fun i => (clearSlots b m i).map Card.rank)).length =
        (l.filterMap (clearSlots b m)).length by
      have := h (List.finRange 9)
      simp only [Multiset.coe_card]
      exact this
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.filterMap_cons]
      rcases clearSlots b m a with _ | c
      · simpa
      · simpa
  -- countP None = 9 - occupied: use length partition
  have hpart : ∀ (m : Finset (Fin 9)),
      (List.finRange 9).countP (fun i => clearSlots b m i = none) +
      ((List.finRange 9).filterMap (clearSlots b m)).length = 9 := by
    intro m
    -- filterMap.length = countP(isSome)
    have hfm := @List.length_filterMap_eq_countP _ _ (clearSlots b m) (List.finRange 9)
    -- countP(isSome) = countP(≠ none)
    have hiso : (List.finRange 9).countP (fun a => (clearSlots b m a).isSome) =
                (List.finRange 9).countP (fun i => clearSlots b m i ≠ none) := by
      apply List.countP_congr; intro i _; simp [Option.isSome_iff_ne_none]
    -- partition: 9 = countP(= none) + countP(≠ none)
    have hsplit : (List.finRange 9).countP (fun i => clearSlots b m i = none) +
                 (List.finRange 9).countP (fun i => clearSlots b m i ≠ none) = 9 := by
      have h := @List.length_eq_countP_add_countP _ (fun i => decide (clearSlots b m i = none)) (List.finRange 9)
      simp only [List.length_finRange, decide_eq_true_eq] at h
      have hne : (List.finRange 9).countP (fun i => ¬clearSlots b m i = none) =
                 (List.finRange 9).countP (fun i => clearSlots b m i ≠ none) := by
        apply List.countP_congr; intro i _; simp [Ne]
      rw [hne] at h; omega
    rw [hfm, hiso]; omega
  linarith [hpart m₁, hpart m₂, hcard_occ m₁ ▸ hcard_occ m₂ ▸ hcard]

/-- Two moves with equal Option-rank multisets (over m.val) have equal filterMap ranks. -/
private lemma filterMap_ranks_of_map_eq (m₁ m₂ : Finset (Fin 9)) (b : Board)
    (h : m₁.val.map (fun i => (b i).map Card.rank) =
         m₂.val.map (fun i => (b i).map Card.rank)) :
    (m₁.val.filterMap (fun i => (b i).map Card.rank) : Multiset Rank) =
    (m₂.val.filterMap (fun i => (b i).map Card.rank) : Multiset Rank) := by
  -- filterMap f s = filterMap id (map f s) by filterMap_map (with g = id)
  -- so filterMap f m₁ = filterMap id (map f m₁) = filterMap id (map f m₂) = filterMap f m₂
  have key : ∀ (s : Multiset (Fin 9)),
      s.filterMap (fun i => (b i).map Card.rank) =
      (s.map (fun i => (b i).map Card.rank)).filterMap id := by
    intro s
    rw [Multiset.filterMap_map]
    rfl
  rw [key m₁.val, key m₂.val, h]

/-- Simpler interface: two moves of the same size applied to the same state
    produce equal rank-states if they remove the same multiset of ranks.
    (Used for num-pair and face-triple cases in the shared-slot lemma.) -/
private lemma rankState_eq_same_size_same_ranks (s : GameState) (m₁ m₂ : Move)
    (hsize : m₁.card = m₂.card)
    (hranks_eq : (m₁.val.map (fun i => (s.board i).map Card.rank)) =
                 (m₂.val.map (fun i => (s.board i).map Card.rank))) :
    rankState (applyMove s m₁) = rankState (applyMove s m₂) := by
  -- Equal filterMap ranks (Some parts) from the equal Option maps
  have hfilter_eq : (m₁.val.filterMap (fun i => (s.board i).map Card.rank) : Multiset Rank) =
                    (m₂.val.filterMap (fun i => (s.board i).map Card.rank) : Multiset Rank) :=
    filterMap_ranks_of_map_eq m₁ m₂ s.board hranks_eq
  -- Empty-slot count after clearing is the same
  have hempty_eq :
      (List.finRange 9).countP (fun i => clearSlots s.board m₁ i = none) =
      (List.finRange 9).countP (fun i => clearSlots s.board m₂ i = none) :=
    clearSlots_empty_count_eq s.board m₁ m₂ hfilter_eq
  -- pileRanks are equal (same pile drop count)
  have hpile : (rankState (applyMove s m₁)).pileRanks = (rankState (applyMove s m₂)).pileRanks := by
    simp only [rankState, applyMove]
    congr 1
    rw [refill_pile, refill_pile, hempty_eq]
  -- boardRanks filterMap is equal (from clearSlots_filterMap_rank_add + hfilter_eq)
  have hboard_fm :
      ((List.finRange 9).filterMap (fun i => (clearSlots s.board m₁ i).map Card.rank)
        : Multiset Rank) =
      ((List.finRange 9).filterMap (fun i => (clearSlots s.board m₂ i).map Card.rank)
        : Multiset Rank) := by
    have h₁ := clearSlots_filterMap_rank_add s.board m₁
    have h₂ := clearSlots_filterMap_rank_add s.board m₂
    -- h₁: cs₁ + m₁.fm = board; h₂: cs₂ + m₂.fm = board; m₁.fm = m₂.fm
    -- → cs₁ + m₁.fm = cs₂ + m₁.fm → cs₁ = cs₂
    have heq : ((List.finRange 9).filterMap (fun i => (clearSlots s.board m₁ i).map Card.rank)
          : Multiset Rank) +
        (m₁.val.filterMap (fun i => (s.board i).map Card.rank) : Multiset Rank) =
        ((List.finRange 9).filterMap (fun i => (clearSlots s.board m₂ i).map Card.rank)
          : Multiset Rank) +
        (m₁.val.filterMap (fun i => (s.board i).map Card.rank) : Multiset Rank) := by
      rw [h₁, hfilter_eq, h₂]
    exact Multiset.add_left_inj.mp heq
  -- boardRanks equality after refill (using refill_rank_total)
  have hboard : (rankState (applyMove s m₁)).boardRanks = (rankState (applyMove s m₂)).boardRanks := by
    have htot₁ := refill_rank_total (clearSlots s.board m₁) s.pile
    have htot₂ := refill_rank_total (clearSlots s.board m₂) s.pile
    simp only [rankState, applyMove] at *
    -- total₁ = board₁ + pile₁; total₂ = board₂ + pile₂; total₁ = total₂ (via hboard_fm + pile same)
    have hpile_fm : ((refill (clearSlots s.board m₁) s.pile).2.map Card.rank : Multiset Rank) =
                    ((refill (clearSlots s.board m₂) s.pile).2.map Card.rank : Multiset Rank) := by
      rw [refill_pile, refill_pile, hempty_eq]
    -- board₁ + pile₁_ranks = board_clear₁_ranks + pile_ranks = board_clear₂_ranks + pile_ranks = board₂ + pile₂_ranks
    rw [hboard_fm] at htot₁
    -- htot₁: board₁ + pile₁ = board_clear₂ + pile
    -- htot₂: board₂ + pile₂ = board_clear₂ + pile
    -- So board₁ + pile₁ = board₂ + pile₂, and pile₁ = pile₂, hence board₁ = board₂
    have : ((List.finRange 9).filterMap
            (fun i => ((refill (clearSlots s.board m₁) s.pile).1 i).map Card.rank) : Multiset Rank) +
           ((refill (clearSlots s.board m₁) s.pile).2.map Card.rank : Multiset Rank) =
           ((List.finRange 9).filterMap
            (fun i => ((refill (clearSlots s.board m₂) s.pile).1 i).map Card.rank) : Multiset Rank) +
           ((refill (clearSlots s.board m₂) s.pile).2.map Card.rank : Multiset Rank) := by
      rw [htot₁, htot₂]
    rw [hpile_fm] at this
    exact Multiset.add_left_inj.mp this
  -- Combine boardRanks and pileRanks into full rankState equality
  cases hrk₁ : rankState (applyMove s m₁)
  cases hrk₂ : rankState (applyMove s m₂)
  simp only [hrk₁, hrk₂] at hboard hpile
  simp only [hrk₁, hrk₂, hboard, hpile]

/-! ## Lemma 2 helper: pile suffix is shared under disjoint moves -/

/-- Helper: countP_none + filterMap.length = 9 for finRange 9, for any board-like function. -/
lemma countP_none_add_filterMap_eq_nine (f : Fin 9 → Option Card) :
    (List.finRange 9).countP (fun i => f i = none) +
    (List.finRange 9 |>.filterMap f).length = 9 := by
  have h := @List.length_eq_countP_add_countP _ (fun i => decide (f i = none)) (List.finRange 9)
  simp only [List.length_finRange, decide_eq_true_eq] at h
  have hfm := @List.length_filterMap_eq_countP _ _ f (List.finRange 9)
  have hiso : (List.finRange 9).countP (fun i => ¬f i = none) =
              (List.finRange 9).countP (fun i => (f i).isSome) := by
    apply List.countP_congr; intro i _; simp [Option.isSome_iff_ne_none]
  omega

/-- Clearing all slots in m sets them to none, increasing the none-count by m.card,
    provided all those slots were occupied. -/
private lemma clearSlots_countP_none_add (b : Board) (m : Finset (Fin 9))
    (hall : ∀ i ∈ m, b i ≠ none) :
    (List.finRange 9).countP (fun i => clearSlots b m i = none) =
    (List.finRange 9).countP (fun i => b i = none) + m.card := by
  induction m using Finset.induction with
  | empty => simp [clearSlots]
  | @insert a s' ha ih =>
    have hall_s' : ∀ i ∈ s', b i ≠ none := fun i hi => hall i (Finset.mem_insert_of_mem hi)
    have hall_a : b a ≠ none := hall a (Finset.mem_insert_self a s')
    rw [Finset.card_insert_of_notMem ha, clearSlots_eq_update' b a s']
    have hclear_a : clearSlots b s' a ≠ none := by
      simp only [clearSlots, if_neg ha]; exact hall_a
    -- countP_none(update f a none) = countP_none(f) + 1 when f a ≠ none
    have hstep : (List.finRange 9).countP (fun i => Function.update (clearSlots b s') a none i = none) =
                 (List.finRange 9).countP (fun i => clearSlots b s' i = none) + 1 := by
      have hfm := filterMap_clearSlot_length _ a hclear_a
      linarith [countP_none_add_filterMap_eq_nine (Function.update (clearSlots b s') a none),
                countP_none_add_filterMap_eq_nine (clearSlots b s')]
    rw [hstep, ih hall_s']
    omega

/-- The empty-slot count of `(refill b pile).1` is `countP_none(b) - min(countP_none(b), pile.length)`. -/
private lemma refill_countP_none (b : Board) (pile : List Card) :
    (List.finRange 9).countP (fun i => (refill b pile).1 i = none) =
    (List.finRange 9).countP (fun i => b i = none) -
    min ((List.finRange 9).countP (fun i => b i = none)) pile.length := by
  have hcons := refill_conserves' b pile
  have hpile_len : (refill b pile).2.length =
      pile.length - min ((List.finRange 9).countP (fun i => b i = none)) pile.length := by
    rw [refill_pile, List.length_drop]
  have h1 := countP_none_add_filterMap_eq_nine (refill b pile).1
  have h2 := countP_none_add_filterMap_eq_nine b
  omega

/-- Two disjoint legal moves applied in either order yield the same pile suffix.
    See docs/proof/confluence.md §2, Lemma 2. -/
private lemma disjoint_applyMove_pile_eq (s : GameState) (m₁ m₂ : Move)
    (h₁ : IsLegal s m₁) (h₂ : IsLegal s m₂)
    (hdisj : Disjoint m₁ m₂) :
    (applyMove (applyMove s m₁) m₂).pile = (applyMove (applyMove s m₂) m₁).pile := by
  -- Both sides equal s.pile.drop(min(N + m₁.card + m₂.card, P)) where
  -- N = countP_none(s.board), P = s.pile.length
  set N := (List.finRange 9).countP (fun i => s.board i = none)
  set P := s.pile.length
  -- Slots occupied in s that are in m₂ remain occupied in (applyMove s m₁) and vice versa
  have h₁₂_occ : ∀ i ∈ m₂, (applyMove s m₁).board i ≠ none := by
    intro i hi
    have hnotin : i ∉ m₁ := Finset.disjoint_right.mp hdisj hi
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (legal_slots_occupied' s m₂ h₂ i hi)
    exact Option.ne_none_iff_exists'.mpr ⟨c, applyMove_board_of_some_notin s m₁ i c hnotin hc⟩
  have h₂₁_occ : ∀ i ∈ m₁, (applyMove s m₂).board i ≠ none := by
    intro i hi
    have hnotin : i ∉ m₂ := Finset.disjoint_left.mp hdisj hi
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (legal_slots_occupied' s m₁ h₁ i hi)
    exact Option.ne_none_iff_exists'.mpr ⟨c, applyMove_board_of_some_notin s m₂ i c hnotin hc⟩
  -- Helper: pile for a single move application
  have pile_of_applyMove : ∀ (t : GameState) (m : Move) (hall : ∀ i ∈ m, t.board i ≠ none),
      (applyMove t m).pile = t.pile.drop
        (min ((List.finRange 9).countP (fun i => t.board i = none) + m.card) t.pile.length) := by
    intro t m hall
    show (refill (clearSlots t.board m) t.pile).2 = _
    rw [refill_pile, clearSlots_countP_none_add t.board m hall]
  -- Helper: countP_none for a single move application
  have none_of_applyMove : ∀ (t : GameState) (m : Move) (hall : ∀ i ∈ m, t.board i ≠ none),
      (List.finRange 9).countP (fun i => (applyMove t m).board i = none) =
      (List.finRange 9).countP (fun i => t.board i = none) + m.card -
      min ((List.finRange 9).countP (fun i => t.board i = none) + m.card) t.pile.length := by
    intro t m hall
    show (List.finRange 9).countP (fun i => (refill (clearSlots t.board m) t.pile).1 i = none) = _
    rw [refill_countP_none, clearSlots_countP_none_add t.board m hall]
  -- Pile after first move m₁
  have hpile₁ : (applyMove s m₁).pile = s.pile.drop (min (N + m₁.card) P) :=
    pile_of_applyMove s m₁ (legal_slots_occupied' s m₁ h₁)
  -- Pile length after first move m₁
  have hplen₁ : (applyMove s m₁).pile.length = P - min (N + m₁.card) P := by
    rw [hpile₁, List.length_drop]
  -- countP_none of (applyMove s m₁).board
  have hN₁ : (List.finRange 9).countP (fun i => (applyMove s m₁).board i = none) =
             N + m₁.card - min (N + m₁.card) P :=
    none_of_applyMove s m₁ (legal_slots_occupied' s m₁ h₁)
  -- Pile after second move m₂ (applied after m₁)
  have hpile₁₂ : (applyMove (applyMove s m₁) m₂).pile =
      (applyMove s m₁).pile.drop
        (min ((List.finRange 9).countP (fun i => (applyMove s m₁).board i = none) + m₂.card)
             (applyMove s m₁).pile.length) :=
    pile_of_applyMove (applyMove s m₁) m₂ h₁₂_occ
  -- Combine: total drop from s.pile
  rw [hpile₁₂, hN₁, hplen₁, hpile₁, List.drop_drop]
  -- Symmetric side (m₂ then m₁)
  have hpile₂ : (applyMove s m₂).pile = s.pile.drop (min (N + m₂.card) P) :=
    pile_of_applyMove s m₂ (legal_slots_occupied' s m₂ h₂)
  have hplen₂ : (applyMove s m₂).pile.length = P - min (N + m₂.card) P := by
    rw [hpile₂, List.length_drop]
  have hN₂ : (List.finRange 9).countP (fun i => (applyMove s m₂).board i = none) =
             N + m₂.card - min (N + m₂.card) P :=
    none_of_applyMove s m₂ (legal_slots_occupied' s m₂ h₂)
  have hpile₂₁ : (applyMove (applyMove s m₂) m₁).pile =
      (applyMove s m₂).pile.drop
        (min ((List.finRange 9).countP (fun i => (applyMove s m₂).board i = none) + m₁.card)
             (applyMove s m₂).pile.length) :=
    pile_of_applyMove (applyMove s m₂) m₁ h₂₁_occ
  rw [hpile₂₁, hN₂, hplen₂, hpile₂, List.drop_drop]
  -- Both sides reduce to s.pile.drop(min(N + m₁.card + m₂.card, P)) by omega arithmetic
  congr 1; omega

/-- Helper: `filterMap` is congruent under pointwise function equality on the multiset. -/
private lemma multiset_filterMap_congr {α β : Type*} {f g : α → Option β} {s : Multiset α}
    (h : ∀ x ∈ s, f x = g x) : s.filterMap f = s.filterMap g := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    have ha : f a = g a := h a (Multiset.mem_cons_self a t)
    rcases hfa : f a with _ | b
    · rw [Multiset.filterMap_cons_none a t hfa, Multiset.filterMap_cons_none a t (ha ▸ hfa)]
      exact ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    · rw [Multiset.filterMap_cons_some f a t hfa, Multiset.filterMap_cons_some g a t (ha ▸ hfa)]
      exact congrArg (b ::ₘ ·) (ih (fun x hx => h x (Multiset.mem_cons_of_mem hx)))

/-- Helper: if `∀ x ∈ m, f x = g x`, then `m.val.filterMap f = m.val.filterMap g`. -/
private lemma filterMap_congr' {α β : Type*} (m : Finset α) (f g : α → Option β)
    (h : ∀ x ∈ m, f x = g x) :
    m.val.filterMap f = m.val.filterMap g :=
  multiset_filterMap_congr (fun x hx => h x (Finset.mem_def.mpr hx))

/-- Two disjoint legal moves applied in either order yield the same board rank-multiset. -/
private lemma disjoint_applyMove_boardRanks_eq (s : GameState) (m₁ m₂ : Move)
    (h₁ : IsLegal s m₁) (h₂ : IsLegal s m₂)
    (hdisj : Disjoint m₁ m₂) :
    (rankState (applyMove (applyMove s m₁) m₂)).boardRanks =
    (rankState (applyMove (applyMove s m₂) m₁)).boardRanks := by
  -- m₂ slots are preserved by m₁ (disjoint), so the rank filterMap is the same as on s.board.
  -- State in unfolded applyMove form so it matches clearSlots_filterMap_rank_add.
  have hm₂_eq : (m₂.val.filterMap (fun i => ((refill (clearSlots s.board m₁) s.pile).1 i).map Card.rank)
                  : Multiset Rank) =
                m₂.val.filterMap (fun i => (s.board i).map Card.rank) :=
    filterMap_congr' m₂ _ _ (fun i hi => by
      have hnotin : i ∉ m₁ := Finset.disjoint_right.mp hdisj hi
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (legal_slots_occupied' s m₂ h₂ i hi)
      have hboard : (applyMove s m₁).board i = some c :=
        applyMove_board_of_some_notin s m₁ i c hnotin hc
      simp only [applyMove] at hboard
      simp [hboard, hc])
  have hm₁_eq : (m₁.val.filterMap (fun i => ((refill (clearSlots s.board m₂) s.pile).1 i).map Card.rank)
                  : Multiset Rank) =
                m₁.val.filterMap (fun i => (s.board i).map Card.rank) :=
    filterMap_congr' m₁ _ _ (fun i hi => by
      have hnotin : i ∉ m₂ := Finset.disjoint_left.mp hdisj hi
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (legal_slots_occupied' s m₁ h₁ i hi)
      have hboard : (applyMove s m₂).board i = some c :=
        applyMove_board_of_some_notin s m₂ i c hnotin hc
      simp only [applyMove] at hboard
      simp [hboard, hc])
  -- Rank-conservation equations
  have htot₁ := refill_rank_total (clearSlots s.board m₁) s.pile
  have htot₂ := refill_rank_total (clearSlots s.board m₂) s.pile
  have htot₁₂ := refill_rank_total (clearSlots (refill (clearSlots s.board m₁) s.pile).1 m₂)
                                    (refill (clearSlots s.board m₁) s.pile).2
  have htot₂₁ := refill_rank_total (clearSlots (refill (clearSlots s.board m₂) s.pile).1 m₁)
                                    (refill (clearSlots s.board m₂) s.pile).2
  have hclear₁ := clearSlots_filterMap_rank_add s.board m₁
  have hclear₂ := clearSlots_filterMap_rank_add s.board m₂
  have hclear₁₂ : ((List.finRange 9).filterMap
                    (fun i => (clearSlots (refill (clearSlots s.board m₁) s.pile).1 m₂ i).map Card.rank)
                  : Multiset Rank) +
                  m₂.val.filterMap (fun i => (s.board i).map Card.rank) =
                  (List.finRange 9).filterMap
                    (fun i => ((refill (clearSlots s.board m₁) s.pile).1 i).map Card.rank) := by
    have := clearSlots_filterMap_rank_add (refill (clearSlots s.board m₁) s.pile).1 m₂
    rwa [hm₂_eq] at this
  have hclear₂₁ : ((List.finRange 9).filterMap
                    (fun i => (clearSlots (refill (clearSlots s.board m₂) s.pile).1 m₁ i).map Card.rank)
                  : Multiset Rank) +
                  m₁.val.filterMap (fun i => (s.board i).map Card.rank) =
                  (List.finRange 9).filterMap
                    (fun i => ((refill (clearSlots s.board m₂) s.pile).1 i).map Card.rank) := by
    have := clearSlots_filterMap_rank_add (refill (clearSlots s.board m₂) s.pile).1 m₁
    rwa [hm₁_eq] at this
  -- pile ranks are equal (from disjoint_applyMove_pile_eq)
  have hpile_eq : ((refill (clearSlots (refill (clearSlots s.board m₁) s.pile).1 m₂)
                          (refill (clearSlots s.board m₁) s.pile).2).2.map Card.rank
                  : Multiset Rank) =
                  (refill (clearSlots (refill (clearSlots s.board m₂) s.pile).1 m₁)
                          (refill (clearSlots s.board m₂) s.pile).2).2.map Card.rank := by
    have heq := disjoint_applyMove_pile_eq s m₁ m₂ h₁ h₂ hdisj
    simp only [applyMove] at heq
    exact congrArg (↑· : List Rank → Multiset Rank) (congrArg (List.map Card.rank) heq)
  -- Board ranks + pile ranks = total (both orderings telescope to same total)
  -- LHS side: BR₁₂ + PR₁₂ + R₁ + R₂ = total
  have hlhs : ((List.finRange 9).filterMap
                (fun i => ((refill (clearSlots (refill (clearSlots s.board m₁) s.pile).1 m₂)
                           (refill (clearSlots s.board m₁) s.pile).2).1 i).map Card.rank)
              : Multiset Rank) +
              (refill (clearSlots (refill (clearSlots s.board m₁) s.pile).1 m₂)
                     (refill (clearSlots s.board m₁) s.pile).2).2.map Card.rank +
              m₁.val.filterMap (fun i => (s.board i).map Card.rank) +
              m₂.val.filterMap (fun i => (s.board i).map Card.rank) =
              (List.finRange 9).filterMap (fun i => (s.board i).map Card.rank) +
              s.pile.map Card.rank := by
    calc ((List.finRange 9).filterMap
              (fun i => ((refill (clearSlots (refill (clearSlots s.board m₁) s.pile).1 m₂)
                         (refill (clearSlots s.board m₁) s.pile).2).1 i).map Card.rank)
          : Multiset Rank) +
         (refill (clearSlots (refill (clearSlots s.board m₁) s.pile).1 m₂)
                (refill (clearSlots s.board m₁) s.pile).2).2.map Card.rank +
         m₁.val.filterMap (fun i => (s.board i).map Card.rank) +
         m₂.val.filterMap (fun i => (s.board i).map Card.rank)
        = ((List.finRange 9).filterMap
              (fun i => (clearSlots (refill (clearSlots s.board m₁) s.pile).1 m₂ i).map Card.rank) +
           (refill (clearSlots s.board m₁) s.pile).2.map Card.rank) +
          m₁.val.filterMap (fun i => (s.board i).map Card.rank) +
          m₂.val.filterMap (fun i => (s.board i).map Card.rank) := by rw [htot₁₂]
      _ = (List.finRange 9).filterMap
              (fun i => (clearSlots (refill (clearSlots s.board m₁) s.pile).1 m₂ i).map Card.rank) +
          m₂.val.filterMap (fun i => (s.board i).map Card.rank) +
          (refill (clearSlots s.board m₁) s.pile).2.map Card.rank +
          m₁.val.filterMap (fun i => (s.board i).map Card.rank) := by abel
      _ = (List.finRange 9).filterMap
              (fun i => ((refill (clearSlots s.board m₁) s.pile).1 i).map Card.rank) +
          (refill (clearSlots s.board m₁) s.pile).2.map Card.rank +
          m₁.val.filterMap (fun i => (s.board i).map Card.rank) := by rw [hclear₁₂]
      _ = ((List.finRange 9).filterMap (fun i => (clearSlots s.board m₁ i).map Card.rank) +
           s.pile.map Card.rank) +
          m₁.val.filterMap (fun i => (s.board i).map Card.rank) := by rw [htot₁]
      _ = (List.finRange 9).filterMap (fun i => (clearSlots s.board m₁ i).map Card.rank) +
          m₁.val.filterMap (fun i => (s.board i).map Card.rank) +
          s.pile.map Card.rank := by abel
      _ = (List.finRange 9).filterMap (fun i => (s.board i).map Card.rank) +
          s.pile.map Card.rank := by rw [hclear₁]
  -- RHS side: BR₂₁ + PR₂₁ + R₁ + R₂ = total
  have hrhs : ((List.finRange 9).filterMap
                (fun i => ((refill (clearSlots (refill (clearSlots s.board m₂) s.pile).1 m₁)
                           (refill (clearSlots s.board m₂) s.pile).2).1 i).map Card.rank)
              : Multiset Rank) +
              (refill (clearSlots (refill (clearSlots s.board m₂) s.pile).1 m₁)
                     (refill (clearSlots s.board m₂) s.pile).2).2.map Card.rank +
              m₁.val.filterMap (fun i => (s.board i).map Card.rank) +
              m₂.val.filterMap (fun i => (s.board i).map Card.rank) =
              (List.finRange 9).filterMap (fun i => (s.board i).map Card.rank) +
              s.pile.map Card.rank := by
    calc ((List.finRange 9).filterMap
              (fun i => ((refill (clearSlots (refill (clearSlots s.board m₂) s.pile).1 m₁)
                         (refill (clearSlots s.board m₂) s.pile).2).1 i).map Card.rank)
          : Multiset Rank) +
         (refill (clearSlots (refill (clearSlots s.board m₂) s.pile).1 m₁)
                (refill (clearSlots s.board m₂) s.pile).2).2.map Card.rank +
         m₁.val.filterMap (fun i => (s.board i).map Card.rank) +
         m₂.val.filterMap (fun i => (s.board i).map Card.rank)
        = ((List.finRange 9).filterMap
              (fun i => (clearSlots (refill (clearSlots s.board m₂) s.pile).1 m₁ i).map Card.rank) +
           (refill (clearSlots s.board m₂) s.pile).2.map Card.rank) +
          m₁.val.filterMap (fun i => (s.board i).map Card.rank) +
          m₂.val.filterMap (fun i => (s.board i).map Card.rank) := by rw [htot₂₁]
      _ = (List.finRange 9).filterMap
              (fun i => (clearSlots (refill (clearSlots s.board m₂) s.pile).1 m₁ i).map Card.rank) +
          m₁.val.filterMap (fun i => (s.board i).map Card.rank) +
          (refill (clearSlots s.board m₂) s.pile).2.map Card.rank +
          m₂.val.filterMap (fun i => (s.board i).map Card.rank) := by abel
      _ = (List.finRange 9).filterMap
              (fun i => ((refill (clearSlots s.board m₂) s.pile).1 i).map Card.rank) +
          (refill (clearSlots s.board m₂) s.pile).2.map Card.rank +
          m₂.val.filterMap (fun i => (s.board i).map Card.rank) := by rw [hclear₂₁]
      _ = ((List.finRange 9).filterMap (fun i => (clearSlots s.board m₂ i).map Card.rank) +
           s.pile.map Card.rank) +
          m₂.val.filterMap (fun i => (s.board i).map Card.rank) := by rw [htot₂]
      _ = (List.finRange 9).filterMap (fun i => (clearSlots s.board m₂ i).map Card.rank) +
          m₂.val.filterMap (fun i => (s.board i).map Card.rank) +
          s.pile.map Card.rank := by abel
      _ = (List.finRange 9).filterMap (fun i => (s.board i).map Card.rank) +
          s.pile.map Card.rank := by rw [hclear₂]
  -- Cancel R₁ and R₂: both sides + R₁ + R₂ = same total → board+pile equal
  have hsum_eq : ((List.finRange 9).filterMap
                    (fun i => ((refill (clearSlots (refill (clearSlots s.board m₁) s.pile).1 m₂)
                               (refill (clearSlots s.board m₁) s.pile).2).1 i).map Card.rank)
                  : Multiset Rank) +
                 (refill (clearSlots (refill (clearSlots s.board m₁) s.pile).1 m₂)
                         (refill (clearSlots s.board m₁) s.pile).2).2.map Card.rank =
                 (List.finRange 9).filterMap
                   (fun i => ((refill (clearSlots (refill (clearSlots s.board m₂) s.pile).1 m₁)
                              (refill (clearSlots s.board m₂) s.pile).2).1 i).map Card.rank) +
                 (refill (clearSlots (refill (clearSlots s.board m₂) s.pile).1 m₁)
                         (refill (clearSlots s.board m₂) s.pile).2).2.map Card.rank :=
    add_right_cancel (add_right_cancel (hlhs.trans hrhs.symm))
  -- Connect goal's rankState.boardRanks to concrete filterMap via simp, then cancel pile.
  -- Use higher heartbeat limit because unfolding applyMove in double-move state is expensive.
  -- Use the fact that rankState.boardRanks = List.filterMap (fun i => s.board i |>.map Card.rank)
  -- (up to the ·.rank = Card.rank identification), then use applyMove_board to
  -- convert (applyMove (applyMove s m₁) m₂).board to the concrete refill form.
  have h_board₁₂ : (rankState (applyMove (applyMove s m₁) m₂)).boardRanks =
      ((List.finRange 9).filterMap (fun i =>
         ((applyMove (applyMove s m₁) m₂).board i).map Card.rank)
      : Multiset Rank) := by simp only [rankState]
  have h_board₂₁ : (rankState (applyMove (applyMove s m₂) m₁)).boardRanks =
      ((List.finRange 9).filterMap (fun i =>
         ((applyMove (applyMove s m₂) m₁).board i).map Card.rank)
      : Multiset Rank) := by simp only [rankState]
  rw [h_board₁₂, h_board₂₁]
  simp_rw [applyMove_board_eq, applyMove_pile_eq]
  rw [← hpile_eq] at hsum_eq
  exact Multiset.add_left_inj.mp hsum_eq

/-- If a legal move exists, `remaining` strictly decreases. -/
lemma remaining_applyMove_lt (s : GameState) (m : Move)
    (h : IsLegal s m) : remaining (applyMove s m) < remaining s := by
  have heq : remaining (applyMove s m) + m.card = remaining s := by
    simp only [remaining, applyMove]
    linarith [refill_conserves' (clearSlots s.board m) s.pile,
              clearSlots_occupied_length s.board m (legal_slots_occupied' s m h)]
  linarith [legal_move_card_pos' s m h]

/-- Cross-state rankState equality after applying moves that remove the same ranks.
    If two states have equal rank-states, and two moves (one per state) remove the
    same multiset of ranks from occupied slots, then the resulting rank-states are equal. -/
private lemma applyMove_rankState_eq_cross
    (s₁ s₂ : GameState) (m₁ m₂ : Move)
    (hboardRanks : (rankState s₁).boardRanks = (rankState s₂).boardRanks)
    (hpileRanks : (rankState s₁).pileRanks = (rankState s₂).pileRanks)
    (hcard : m₁.card = m₂.card)
    (hocc₁ : ∀ i ∈ m₁, s₁.board i ≠ none)
    (hocc₂ : ∀ i ∈ m₂, s₂.board i ≠ none)
    (hranks : (m₁.val.filterMap (fun i => (s₁.board i).map Card.rank) : Multiset Rank) =
              m₂.val.filterMap (fun i => (s₂.board i).map Card.rank)) :
    rankState (applyMove s₁ m₁) = rankState (applyMove s₂ m₂) := by
  -- Unfold boardRanks and pileRanks hypotheses to concrete filterMap form
  simp only [rankState] at hboardRanks hpileRanks
  -- hboardRanks : ↑(filterMap rank finRange s₁) = ↑(filterMap rank finRange s₂)
  -- hpileRanks  : s₁.pile.map rank = s₂.pile.map rank
  -- Occupied-slot count equality: length(filterMap b) = card(boardRanks)
  have hfm_len_eq : ∀ (s : GameState),
      (List.finRange 9 |>.filterMap s.board).length =
      ((List.finRange 9).filterMap (fun i => (s.board i).map Card.rank) : Multiset Rank).card := by
    intro s
    simp only [Multiset.coe_card]
    induction (List.finRange 9) with
    | nil => simp
    | cons a t ih => simp only [List.filterMap_cons]; cases s.board a <;> simp [ih]
  have hempty_eq : (List.finRange 9).countP (fun i => s₁.board i = none) =
                   (List.finRange 9).countP (fun i => s₂.board i = none) := by
    have hlen_eq : (List.finRange 9 |>.filterMap s₁.board).length =
                   (List.finRange 9 |>.filterMap s₂.board).length := by
      rw [hfm_len_eq s₁, hfm_len_eq s₂]; exact congrArg Multiset.card hboardRanks
    linarith [countP_none_add_filterMap_eq_nine s₁.board, countP_none_add_filterMap_eq_nine s₂.board]
  -- Pile lengths are equal
  have hplen_eq : s₁.pile.length = s₂.pile.length := by
    have h := congrArg List.length hpileRanks
    simp only [List.length_map] at h
    exact h
  -- Drop counts after clearing are equal
  have hempty_clear_eq :
      (List.finRange 9).countP (fun i => clearSlots s₁.board m₁ i = none) =
      (List.finRange 9).countP (fun i => clearSlots s₂.board m₂ i = none) := by
    rw [clearSlots_countP_none_add s₁.board m₁ hocc₁,
        clearSlots_countP_none_add s₂.board m₂ hocc₂,
        hempty_eq, hcard]
  -- pileRanks equality for the two results
  have hpile_out :
      (rankState (applyMove s₁ m₁)).pileRanks = (rankState (applyMove s₂ m₂)).pileRanks := by
    simp only [rankState, applyMove]
    rw [refill_pile, refill_pile, hempty_clear_eq, hplen_eq]
    rw [List.map_drop, List.map_drop, hpileRanks]
  -- boardRanks equality: use refill_rank_total + clearSlots_filterMap_rank_add
  have hboard_out :
      (rankState (applyMove s₁ m₁)).boardRanks = (rankState (applyMove s₂ m₂)).boardRanks := by
    have htot₁ := refill_rank_total (clearSlots s₁.board m₁) s₁.pile
    have htot₂ := refill_rank_total (clearSlots s₂.board m₂) s₂.pile
    have hclear₁ := clearSlots_filterMap_rank_add s₁.board m₁
    have hclear₂ := clearSlots_filterMap_rank_add s₂.board m₂
    simp only [rankState, applyMove]
    -- clearSlots multiset equality: cs₁ + rm₁ = board₁ = board₂ = cs₂ + rm₂
    -- and rm₁ = rm₂ (by hranks), so cs₁ = cs₂
    have hcs_eq : ((List.finRange 9).filterMap (fun i => (clearSlots s₁.board m₁ i).map Card.rank)
                   : Multiset Rank) =
                  (List.finRange 9).filterMap (fun i => (clearSlots s₂.board m₂ i).map Card.rank) := by
      apply Multiset.add_left_inj.mp
      calc ((List.finRange 9).filterMap (fun i => (clearSlots s₁.board m₁ i).map Card.rank)
              : Multiset Rank) +
             (m₁.val.filterMap (fun i => (s₁.board i).map Card.rank) : Multiset Rank)
          = (List.finRange 9).filterMap (fun i => (s₁.board i).map Card.rank) := hclear₁
        _ = (List.finRange 9).filterMap (fun i => (s₂.board i).map Card.rank) := hboardRanks
        _ = ((List.finRange 9).filterMap (fun i => (clearSlots s₂.board m₂ i).map Card.rank)
              : Multiset Rank) +
             (m₂.val.filterMap (fun i => (s₂.board i).map Card.rank) : Multiset Rank) := hclear₂.symm
        _ = ((List.finRange 9).filterMap (fun i => (clearSlots s₂.board m₂ i).map Card.rank)
              : Multiset Rank) +
             (m₁.val.filterMap (fun i => (s₁.board i).map Card.rank) : Multiset Rank) := by rw [hranks]
    -- pile output ranks are equal (as Multiset Rank, cast from List Rank via hpile_out)
    have hpile_out_map : ((refill (clearSlots s₁.board m₁) s₁.pile).2.map Card.rank : Multiset Rank) =
                         (refill (clearSlots s₂.board m₂) s₂.pile).2.map Card.rank := by
      have h := hpile_out
      simp only [rankState] at h
      rw [applyMove_pile_eq, applyMove_pile_eq] at h
      exact congrArg (↑· : List Rank → Multiset Rank) h
    -- total = cs + pile; both totals equal; pile outs equal; so boards equal
    have htot_eq :
        ((List.finRange 9).filterMap (fun i => ((refill (clearSlots s₁.board m₁) s₁.pile).1 i).map Card.rank)
          : Multiset Rank) +
        ((refill (clearSlots s₁.board m₁) s₁.pile).2.map Card.rank : Multiset Rank) =
        ((List.finRange 9).filterMap (fun i => ((refill (clearSlots s₂.board m₂) s₂.pile).1 i).map Card.rank)
          : Multiset Rank) +
        ((refill (clearSlots s₂.board m₂) s₂.pile).2.map Card.rank : Multiset Rank) := by
      rw [htot₁, htot₂, hcs_eq, hpileRanks]
    rw [hpile_out_map] at htot_eq
    exact Multiset.add_left_inj.mp htot_eq
  -- Combine to full rankState equality
  cases hrk₁ : rankState (applyMove s₁ m₁)
  cases hrk₂ : rankState (applyMove s₂ m₂)
  simp only [hrk₁, hrk₂] at hboard_out hpile_out
  simp only [hrk₁, hrk₂, hboard_out, hpile_out]

/-- Helper: filterMap f {a} = {fa} when f a = some fa. -/
private lemma filterMap_singleton_some {α β : Type*} (f : α → Option β) (a : α) (xa : β)
    (ha : f a = some xa) : Multiset.filterMap f ({a} : Multiset α) = {xa} := by
  rw [← Multiset.cons_zero, Multiset.filterMap_cons_some f a 0 ha, Multiset.filterMap_zero,
      Multiset.cons_zero]

/-- Helper: filterMap over a two-element finset with known values. -/
private lemma filterMap_pair_val {α β : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b)
    (f : α → Option β) (xa xb : β) (ha : f a = some xa) (hb : f b = some xb) :
    ({a, b} : Finset α).val.filterMap f = (xa ::ₘ {xb}) := by
  rw [Finset.insert_val_of_notMem (Finset.notMem_singleton.mpr hab), Finset.singleton_val]
  rw [Multiset.filterMap_cons_some f a _ ha]
  exact congrArg (xa ::ₘ ·) (filterMap_singleton_some f b xb hb)

/-- Helper: filterMap over a three-element finset with known values. -/
private lemma filterMap_triple_val {α β : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f : α → Option β) (xa xb xc : β)
    (ha : f a = some xa) (hb : f b = some xb) (hc : f c = some xc) :
    ({a, b, c} : Finset α).val.filterMap f = (xa ::ₘ xb ::ₘ {xc}) := by
  have hbc_fin : b ∉ ({c} : Finset α) := Finset.notMem_singleton.mpr hbc
  have habc_fin : a ∉ ({b, c} : Finset α) := by simp [hab, hac]
  rw [Finset.insert_val_of_notMem habc_fin,
      Finset.insert_val_of_notMem hbc_fin,
      Finset.singleton_val]
  rw [Multiset.filterMap_cons_some f a _ ha,
      Multiset.filterMap_cons_some f b _ hb]
  exact congrArg (xa ::ₘ xb ::ₘ ·) (filterMap_singleton_some f c xc hc)

/-- Given `rankState s₁ = rankState s₂` and a legal move `m` for `s₁`, there exists a
    legal move `m'` for `s₂` that removes the same multiset of ranks and has the same size,
    so `rankState (applyMove s₁ m) = rankState (applyMove s₂ m')`. -/
lemma exists_rank_twin (s₁ s₂ : GameState) (m : Move)
    (hrk : rankState s₁ = rankState s₂)
    (hm : IsLegal s₁ m) :
    ∃ m' : Move, IsLegal s₂ m' ∧
      rankState (applyMove s₁ m) = rankState (applyMove s₂ m') := by
  rcases hm with
    ⟨i, j, c₁, c₂, r₁, r₂, hij, rfl, hbi, hbj, hr₁, hr₂, hpair⟩ |
    ⟨a, b, c, ca, cb, cc, hab, hac, hbc, rfl, hba, hbb, hbc', hca, hcb, hcc⟩
  · -- Num-pair case: m = {i, j} with ranks r₁, r₂ summing to 11
    -- r₁ ≠ r₂ since their values sum to 11 (odd), so 2*r₁ ≠ 11
    have hr_neq : r₁ ≠ r₂ := by
      intro heq; subst heq
      simp only [isLegalPair, numericValue] at hpair; omega
    -- Find slots in s₂ with ranks r₁ and r₂ via mem_boardRanks_iff
    have hr₁_mem : Rank.num r₁ ∈ (rankState s₁).boardRanks := by
      rw [mem_boardRanks_iff]; exact ⟨i, c₁, hbi, hr₁⟩
    have hr₂_mem : Rank.num r₂ ∈ (rankState s₁).boardRanks := by
      rw [mem_boardRanks_iff]; exact ⟨j, c₂, hbj, hr₂⟩
    rw [hrk] at hr₁_mem hr₂_mem
    obtain ⟨i', ci', hbi', hri'⟩ := (mem_boardRanks_iff s₂ (Rank.num r₁)).mp hr₁_mem
    obtain ⟨j', cj', hbj', hrj'⟩ := (mem_boardRanks_iff s₂ (Rank.num r₂)).mp hr₂_mem
    -- i' ≠ j': if equal, ci' = cj' so r₁ = r₂, contradiction
    have hi'j' : i' ≠ j' := by
      intro heq; subst heq
      have : ci' = cj' := Option.some_injective _ (hbi'.symm.trans hbj')
      have : Rank.num r₁ = Rank.num r₂ := hri' ▸ hrj' ▸ congrArg Card.rank this
      exact absurd (Rank.num.inj this) hr_neq
    -- Construct twin move m' = {i', j'}
    refine ⟨{i', j'}, Or.inl ⟨i', j', ci', cj', r₁, r₂, hi'j', rfl, hbi', hbj', hri', hrj', hpair⟩, ?_⟩
    -- Prove rankState equality using the helper
    apply applyMove_rankState_eq_cross
    · exact congrArg RankState.boardRanks hrk
    · exact congrArg RankState.pileRanks hrk
    · simp [Finset.card_pair hij, Finset.card_pair hi'j']
    · intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> simp [*]
    · intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> simp [*]
    · -- ranks removed: both are (Rank.num r₁ ::ₘ {Rank.num r₂})
      have hfi : (fun k => (s₁.board k).map Card.rank) i = some (Rank.num r₁) := by simp [hbi, hr₁]
      have hfj : (fun k => (s₁.board k).map Card.rank) j = some (Rank.num r₂) := by simp [hbj, hr₂]
      have hfi' : (fun k => (s₂.board k).map Card.rank) i' = some (Rank.num r₁) := by simp [hbi', hri']
      have hfj' : (fun k => (s₂.board k).map Card.rank) j' = some (Rank.num r₂) := by simp [hbj', hrj']
      rw [filterMap_pair_val hij _ _ _ hfi hfj, filterMap_pair_val hi'j' _ _ _ hfi' hfj']
  · -- Face-triple case: m = {a, b, c} with J, Q, K
    -- Find slots in s₂ with J, Q, K
    have hJ_mem : Rank.face FaceRank.J ∈ (rankState s₁).boardRanks :=
      (mem_boardRanks_iff s₁ _).mpr ⟨a, ca, hba, hca⟩
    have hQ_mem : Rank.face FaceRank.Q ∈ (rankState s₁).boardRanks :=
      (mem_boardRanks_iff s₁ _).mpr ⟨b, cb, hbb, hcb⟩
    have hK_mem : Rank.face FaceRank.K ∈ (rankState s₁).boardRanks :=
      (mem_boardRanks_iff s₁ _).mpr ⟨c, cc, hbc', hcc⟩
    rw [hrk] at hJ_mem hQ_mem hK_mem
    obtain ⟨a', ca', hba', hca'⟩ := (mem_boardRanks_iff s₂ _).mp hJ_mem
    obtain ⟨b', cb', hbb', hcb'⟩ := (mem_boardRanks_iff s₂ _).mp hQ_mem
    obtain ⟨c', cc', hbc'', hcc'⟩ := (mem_boardRanks_iff s₂ _).mp hK_mem
    -- All three slots distinct (ranks J, Q, K are distinct)
    have ha'b' : a' ≠ b' := by
      intro heq; subst heq
      have : ca' = cb' := Option.some_injective _ (hba'.symm.trans hbb')
      have : Rank.face FaceRank.J = Rank.face FaceRank.Q :=
        hca' ▸ hcb' ▸ congrArg Card.rank this
      exact absurd this (by decide)
    have ha'c' : a' ≠ c' := by
      intro heq; subst heq
      have : ca' = cc' := Option.some_injective _ (hba'.symm.trans hbc'')
      have : Rank.face FaceRank.J = Rank.face FaceRank.K :=
        hca' ▸ hcc' ▸ congrArg Card.rank this
      exact absurd this (by decide)
    have hb'c' : b' ≠ c' := by
      intro heq; subst heq
      have : cb' = cc' := Option.some_injective _ (hbb'.symm.trans hbc'')
      have : Rank.face FaceRank.Q = Rank.face FaceRank.K :=
        hcb' ▸ hcc' ▸ congrArg Card.rank this
      exact absurd this (by decide)
    refine ⟨{a', b', c'}, Or.inr ⟨a', b', c', ca', cb', cc', ha'b', ha'c', hb'c',
              rfl, hba', hbb', hbc'', hca', hcb', hcc'⟩, ?_⟩
    apply applyMove_rankState_eq_cross
    · exact congrArg RankState.boardRanks hrk
    · exact congrArg RankState.pileRanks hrk
    · -- card equality: both are 3
      have hm_card : ({a, b, c} : Finset (Fin 9)).card = 3 := by
        rw [Finset.card_insert_of_notMem (show a ∉ ({b, c} : Finset (Fin 9)) by simp [hab, hac])]
        simp [Finset.card_pair hbc]
      have hm'_card : ({a', b', c'} : Finset (Fin 9)).card = 3 := by
        rw [Finset.card_insert_of_notMem (show a' ∉ ({b', c'} : Finset (Fin 9)) by simp [ha'b', ha'c'])]
        simp [Finset.card_pair hb'c']
      rw [hm_card, hm'_card]
    · intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> simp [*]
    · intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> simp [*]
    · -- ranks removed: both are (J ::ₘ Q ::ₘ {K})
      have hfa : (fun k => (s₁.board k).map Card.rank) a = some (Rank.face FaceRank.J) := by simp [hba, hca]
      have hfb : (fun k => (s₁.board k).map Card.rank) b = some (Rank.face FaceRank.Q) := by simp [hbb, hcb]
      have hfc : (fun k => (s₁.board k).map Card.rank) c = some (Rank.face FaceRank.K) := by simp [hbc', hcc]
      have hfa' : (fun k => (s₂.board k).map Card.rank) a' = some (Rank.face FaceRank.J) := by simp [hba', hca']
      have hfb' : (fun k => (s₂.board k).map Card.rank) b' = some (Rank.face FaceRank.Q) := by simp [hbb', hcb']
      have hfc' : (fun k => (s₂.board k).map Card.rank) c' = some (Rank.face FaceRank.K) := by simp [hbc'', hcc']
      rw [filterMap_triple_val hab hac hbc _ _ _ _ hfa hfb hfc,
          filterMap_triple_val ha'b' ha'c' hb'c' _ _ _ _ hfa' hfb' hfc']

/-! ## Lemma 1: Rank-State Equivalence -/

/-- **Lemma 1.** Two states with equal rank-states are equally winnable.

    Proof: by strong induction on `remaining`. At each step, any legal move
    in s₁ has a rank-identical legal move in s₂ (since legal moves depend only
    on ranks). Applying rank-identical moves from rank-equal states yields
    rank-equal successor states. By induction, successors have equal
    winnability, so the original states do too.

    See docs/proof/confluence.md §2, Lemma 1. -/
theorem rankState_determines_outcome (s₁ s₂ : GameState)
    (h : rankState s₁ = rankState s₂) :
    Winnable s₁ ↔ Winnable s₂ := by
  induction hn : remaining s₁ using Nat.strongRecOn generalizing s₁ s₂ with
  | ind n ih =>
  constructor
  · rintro ⟨moves, hleg, hwin⟩
    cases moves with
    | nil =>
      -- s₁ is already a win; s₂ has the same rank-state so it's also a win
      simp only [List.foldl_nil] at hwin
      refine ⟨[], fun i => Fin.elim0 i, ?_⟩
      simp only [List.foldl_nil]
      rwa [isWin_iff_rankState, ← h, ← isWin_iff_rankState]
    | cons m rest =>
      -- Extract the first move and the rest
      have hm_legal : IsLegal s₁ m := by
        have := hleg ⟨0, Nat.zero_lt_succ _⟩; simp at this; exact this
      have hrest_legal : ∀ i : Fin rest.length,
          IsLegal ((rest.take i.val).foldl applyMove (applyMove s₁ m)) (rest.get i) := by
        intro ⟨k, hk⟩
        have := hleg ⟨k + 1, Nat.succ_lt_succ hk⟩
        simp only [List.take_succ_cons, List.foldl_cons, List.get_cons_succ] at this
        exact this
      have hwin_rest : IsWin (rest.foldl applyMove (applyMove s₁ m)) := by simpa using hwin
      -- Find a rank-twin move m' for s₂
      obtain ⟨m', hm'_legal, hrk_eq⟩ := exists_rank_twin s₁ s₂ m h hm_legal
      -- By IH (strong induction), applyMove s₁ m and applyMove s₂ m' have equal winnability
      have hrem_lt : remaining (applyMove s₁ m) < n := hn ▸ remaining_applyMove_lt s₁ m hm_legal
      have ih_step : Winnable (applyMove s₁ m) ↔ Winnable (applyMove s₂ m') :=
        ih (remaining (applyMove s₁ m)) hrem_lt (applyMove s₁ m) (applyMove s₂ m') hrk_eq rfl
      -- Winnable (applyMove s₁ m) is witnessed by rest
      obtain ⟨moves', hleg', hwin'⟩ := ih_step.mp ⟨rest, hrest_legal, hwin_rest⟩
      -- Build winning sequence for s₂: m' followed by moves'
      exact ⟨m' :: moves',
        fun ⟨k, hk⟩ => match k with
          | 0 => hm'_legal
          | k + 1 => by
              simp only [List.take_succ_cons, List.foldl_cons, List.get_cons_succ]
              exact hleg' ⟨k, Nat.lt_of_succ_lt_succ hk⟩,
        by simpa using hwin'⟩
  · -- ← direction: symmetric using h.symm
    rintro ⟨moves, hleg, hwin⟩
    cases moves with
    | nil =>
      simp only [List.foldl_nil] at hwin
      refine ⟨[], fun i => Fin.elim0 i, ?_⟩
      simp only [List.foldl_nil]
      rwa [isWin_iff_rankState, h, ← isWin_iff_rankState]
    | cons m rest =>
      have hm_legal : IsLegal s₂ m := by
        have := hleg ⟨0, Nat.zero_lt_succ _⟩; simp at this; exact this
      have hrest_legal : ∀ i : Fin rest.length,
          IsLegal ((rest.take i.val).foldl applyMove (applyMove s₂ m)) (rest.get i) := by
        intro ⟨k, hk⟩
        have := hleg ⟨k + 1, Nat.succ_lt_succ hk⟩
        simp only [List.take_succ_cons, List.foldl_cons, List.get_cons_succ] at this
        exact this
      have hwin_rest : IsWin (rest.foldl applyMove (applyMove s₂ m)) := by simpa using hwin
      -- Find a rank-twin move m' for s₁ (using h.symm)
      obtain ⟨m', hm'_legal, hrk_eq⟩ := exists_rank_twin s₂ s₁ m h.symm hm_legal
      -- remaining s₂ = remaining s₁ = n
      have hrem_s₂ : remaining s₂ = n := by
        rw [← hn, remaining_eq_rankState, remaining_eq_rankState, h]
      have hrem_lt' : remaining (applyMove s₁ m') < n := hn ▸ remaining_applyMove_lt s₁ m' hm'_legal
      have ih_step : Winnable (applyMove s₁ m') ↔ Winnable (applyMove s₂ m) :=
        ih (remaining (applyMove s₁ m')) hrem_lt' (applyMove s₁ m') (applyMove s₂ m) hrk_eq.symm rfl
      obtain ⟨moves', hleg', hwin'⟩ := ih_step.mpr ⟨rest, hrest_legal, hwin_rest⟩
      exact ⟨m' :: moves',
        fun ⟨k, hk⟩ => match k with
          | 0 => hm'_legal
          | k + 1 => by
              simp only [List.take_succ_cons, List.foldl_cons, List.get_cons_succ]
              exact hleg' ⟨k, Nat.lt_of_succ_lt_succ hk⟩,
        by simpa using hwin'⟩

/-! ## Lemma 2: Disjoint Move Commutativity -/

/-- **Lemma 2.** Disjoint legal moves commute: applying them in either order
    yields states with equal rank-states.

    See docs/proof/confluence.md §2, Lemma 2. -/
theorem disjoint_moves_commute (s : GameState) (m₁ m₂ : Move)
    (h₁ : IsLegal s m₁) (h₂ : IsLegal s m₂)
    (hdisj : Disjoint m₁ m₂) :
    rankState (applyMove (applyMove s m₁) m₂) =
    rankState (applyMove (applyMove s m₂) m₁) := by
  have hb := disjoint_applyMove_boardRanks_eq s m₁ m₂ h₁ h₂ hdisj
  have hp := disjoint_applyMove_pile_eq s m₁ m₂ h₁ h₂ hdisj
  have hpr : (rankState (applyMove (applyMove s m₁) m₂)).pileRanks =
             (rankState (applyMove (applyMove s m₂) m₁)).pileRanks := by
    simp only [rankState, hp]
  cases r₁ : rankState (applyMove (applyMove s m₁) m₂)
  cases r₂ : rankState (applyMove (applyMove s m₂) m₁)
  simp_all [RankState.mk.injEq]

/-- After a disjoint move m₁, move m₂ remains legal. -/
theorem disjoint_preserves_legality (s : GameState) (m₁ m₂ : Move)
    (h₁ : IsLegal s m₁) (h₂ : IsLegal s m₂)
    (hdisj : Disjoint m₁ m₂) :
    IsLegal (applyMove s m₁) m₂ := by
  rcases h₂ with h₂num | h₂face
  · left
    obtain ⟨i, j, c₁, c₂, r₁, r₂, hij, rfl, hbi, hbj, hr₁, hr₂, hpair⟩ := h₂num
    have hd := Finset.disjoint_right.mp hdisj
    exact ⟨i, j, c₁, c₂, r₁, r₂, hij, rfl,
           applyMove_board_of_some_notin s m₁ i c₁ (hd (by simp)) hbi,
           applyMove_board_of_some_notin s m₁ j c₂ (hd (by simp)) hbj,
           hr₁, hr₂, hpair⟩
  · right
    obtain ⟨a, b, c, ca, cb, cc, hab, hac, hbc, rfl, hba, hbb, hbc', hJ, hQ, hK⟩ := h₂face
    have hd := Finset.disjoint_right.mp hdisj
    exact ⟨a, b, c, ca, cb, cc, hab, hac, hbc, rfl,
           applyMove_board_of_some_notin s m₁ a ca (hd (by simp)) hba,
           applyMove_board_of_some_notin s m₁ b cb (hd (by simp)) hbb,
           applyMove_board_of_some_notin s m₁ c cc (hd (by simp)) hbc',
           hJ, hQ, hK⟩

/-! ## Lemma 3: Shared-Slot Rank Preservation -/

/-- Supporting lemma for Lemma 3: a number-pair move and a face-triple move
    cannot share a board position (numeric and face ranks are disjoint). -/
theorem num_face_moves_disjoint (s : GameState) (m₁ m₂ : Move)
    (h₁ : IsLegalNumMove s m₁) (h₂ : IsLegalFaceMove s m₂) :
    Disjoint m₁ m₂ := by
  obtain ⟨i, j, c₁, c₂, r₁, r₂, _, rfl, hbi, hbj, hr₁, hr₂, _⟩ := h₁
  obtain ⟨a, b, c, ca, cb, cc, _, _, _, rfl, hba, hbb, hbc, hJ, hQ, hK⟩ := h₂
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp₁ hp₂
  -- Slot p has a numeric card (from m₁) and a face card (from m₂): contradiction
  obtain ⟨_, cdnum, hbp_num, hrank_num⟩ : ∃ rn : NumRank, ∃ cd : Card,
      s.board p = some cd ∧ cd.rank = Rank.num rn := by
    rcases hp₁ with rfl | rfl
    · exact ⟨r₁, c₁, hbi, hr₁⟩
    · exact ⟨r₂, c₂, hbj, hr₂⟩
  obtain ⟨_, cdface, hbp_face, hrank_face⟩ : ∃ f : FaceRank, ∃ cd : Card,
      s.board p = some cd ∧ cd.rank = Rank.face f := by
    rcases hp₂ with rfl | rfl | rfl
    · exact ⟨FaceRank.J, ca, hba, hJ⟩
    · exact ⟨FaceRank.Q, cb, hbb, hQ⟩
    · exact ⟨FaceRank.K, cc, hbc, hK⟩
  have heq : cdnum = cdface := Option.some_inj.mp (hbp_num.symm.trans hbp_face)
  rw [heq] at hrank_num
  rw [hrank_num] at hrank_face
  exact Rank.noConfusion hrank_face

private lemma pair_val_map (s : GameState) (x y : Fin 9) (hxy : x ≠ y) (r r' : NumRank)
    (hx : (s.board x).map Card.rank = some (Rank.num r))
    (hy : (s.board y).map Card.rank = some (Rank.num r')) :
    ({x, y} : Finset (Fin 9)).val.map (fun i => (s.board i).map Card.rank) =
    ({some (Rank.num r), some (Rank.num r')} : Multiset (Option Rank)) := by
  have hny : x ∉ ({y} : Multiset (Fin 9)) := by simp [Multiset.mem_singleton, hxy]
  simp only [Finset.insert_val, Finset.singleton_val]
  rw [Multiset.ndinsert_of_notMem hny]
  simp [hx, hy]

private lemma face_val_map (s : GameState) (a b c : Fin 9)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ca cb cc : Card)
    (hba : s.board a = some ca) (hbb : s.board b = some cb) (hbc' : s.board c = some cc)
    (hJ : ca.rank = Rank.face FaceRank.J) (hQ : cb.rank = Rank.face FaceRank.Q)
    (hK : cc.rank = Rank.face FaceRank.K) :
    ({a, b, c} : Finset (Fin 9)).val.map (fun i => (s.board i).map Card.rank) =
    ({some (Rank.face FaceRank.J), some (Rank.face FaceRank.Q),
      some (Rank.face FaceRank.K)} : Multiset (Option Rank)) := by
  have hna : a ∉ Multiset.ndinsert b ({c} : Multiset (Fin 9)) := by
    simp [Multiset.mem_ndinsert, hab, hac]
  have hnb : b ∉ ({c} : Multiset (Fin 9)) := by
    simp [Multiset.mem_singleton, hbc]
  simp only [Finset.insert_val, Finset.singleton_val]
  rw [Multiset.ndinsert_of_notMem hna, Multiset.ndinsert_of_notMem hnb]
  simp [hba, hbb, hbc', hJ, hQ, hK]

private lemma num_num_ranks_eq (s : GameState) (i₁ j₁ i₂ j₂ : Fin 9)
    (c₁ c₂ c₃ c₄ : Card) (r₁ r₁' r₂ r₂' : NumRank)
    (h₁ij : i₁ ≠ j₁) (h₂ij : i₂ ≠ j₂)
    (hbi₁ : s.board i₁ = some c₁) (hbj₁ : s.board j₁ = some c₂)
    (hbi₂ : s.board i₂ = some c₃) (hbj₂ : s.board j₂ = some c₄)
    (hr₁ : c₁.rank = Rank.num r₁) (hr₁' : c₂.rank = Rank.num r₁')
    (hr₂ : c₃.rank = Rank.num r₂) (hr₂' : c₄.rank = Rank.num r₂')
    (hpair₁ : isLegalPair r₁ r₁') (hpair₂ : isLegalPair r₂ r₂')
    (hshared : ¬ Disjoint ({i₁, j₁} : Finset (Fin 9)) {i₂, j₂}) :
    ({i₁, j₁} : Finset (Fin 9)).val.map (fun i => (s.board i).map Card.rank) =
    ({i₂, j₂} : Finset (Fin 9)).val.map (fun i => (s.board i).map Card.rank) := by
  simp only [isLegalPair, numericValue] at hpair₁ hpair₂
  rw [Finset.not_disjoint_iff] at hshared
  obtain ⟨p, hp₁, hp₂⟩ := hshared
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp₁ hp₂
  rw [pair_val_map s i₁ j₁ h₁ij r₁ r₁' (by simp [hbi₁, hr₁]) (by simp [hbj₁, hr₁']),
      pair_val_map s i₂ j₂ h₂ij r₂ r₂' (by simp [hbi₂, hr₂]) (by simp [hbj₂, hr₂'])]
  have hrel : (r₁ = r₂ ∧ r₁' = r₂') ∨ (r₁ = r₂' ∧ r₁' = r₂) := by
    rcases hp₁ with rfl | rfl <;> rcases hp₂ with rfl | rfl
    · have hc : c₁ = c₃ := Option.some_inj.mp (hbi₁.symm.trans hbi₂)
      have hr : r₁ = r₂ := Rank.num.inj (by rw [← hr₁, ← hr₂, hc])
      left; exact ⟨hr, Fin.ext (by have := congr_arg Fin.val hr; omega)⟩
    · have hc : c₁ = c₄ := Option.some_inj.mp (hbi₁.symm.trans hbj₂)
      have hr : r₁ = r₂' := Rank.num.inj (by rw [← hr₁, ← hr₂', hc])
      right; exact ⟨hr, Fin.ext (by have := congr_arg Fin.val hr; omega)⟩
    · have hc : c₂ = c₃ := Option.some_inj.mp (hbj₁.symm.trans hbi₂)
      have hr : r₁' = r₂ := Rank.num.inj (by rw [← hr₁', ← hr₂, hc])
      right; exact ⟨Fin.ext (by have := congr_arg Fin.val hr; omega), hr⟩
    · have hc : c₂ = c₄ := Option.some_inj.mp (hbj₁.symm.trans hbj₂)
      have hr : r₁' = r₂' := Rank.num.inj (by rw [← hr₁', ← hr₂', hc])
      left; exact ⟨Fin.ext (by have := congr_arg Fin.val hr; omega), hr⟩
  rcases hrel with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · simp only [h1, h2]; exact Multiset.pair_comm _ _

/-- **Lemma 3.** Two legal moves sharing a board position yield successor
    states with equal rank-states.

    See docs/proof/confluence.md §2, Lemma 3. -/
theorem shared_slot_rank_preserved (s : GameState) (m₁ m₂ : Move)
    (h₁ : IsLegal s m₁) (h₂ : IsLegal s m₂)
    (hshared : ¬ Disjoint m₁ m₂) :
    rankState (applyMove s m₁) = rankState (applyMove s m₂) := by
  rcases h₁ with h₁num | h₁face <;> rcases h₂ with h₂num | h₂face
  · -- Both numeric pairs: each removes {r, 11-r} from the same position
    obtain ⟨i₁, j₁, c₁, c₂, r₁, r₁', h₁ij, rfl, hbi₁, hbj₁, hr₁, hr₁', hpair₁⟩ := h₁num
    obtain ⟨i₂, j₂, c₃, c₄, r₂, r₂', h₂ij, rfl, hbi₂, hbj₂, hr₂, hr₂', hpair₂⟩ := h₂num
    apply rankState_eq_same_size_same_ranks
    · -- Both numeric moves have size 2
      simp only [Finset.card_pair h₁ij, Finset.card_pair h₂ij]
    · -- Shared position forces both pairs to include the same ranks
      exact num_num_ranks_eq s i₁ j₁ i₂ j₂ c₁ c₂ c₃ c₄ r₁ r₁' r₂ r₂'
        h₁ij h₂ij hbi₁ hbj₁ hbi₂ hbj₂ hr₁ hr₁' hr₂ hr₂' hpair₁ hpair₂ hshared
  · -- Numeric + face: impossible by num_face_moves_disjoint
    exact absurd (num_face_moves_disjoint s m₁ m₂ h₁num h₂face) hshared
  · -- Face + numeric: impossible (symmetric)
    exact absurd (Disjoint.symm (num_face_moves_disjoint s m₂ m₁ h₂num h₁face))
      hshared
  · -- Both face triples: each removes {J, Q, K}
    obtain ⟨a₁, b₁, c₁, ca₁, cb₁, cc₁, ha₁b₁, ha₁c₁, hb₁c₁, rfl,
            hba₁, hbb₁, hbc₁, hJ₁, hQ₁, hK₁⟩ := h₁face
    obtain ⟨a₂, b₂, c₂, ca₂, cb₂, cc₂, ha₂b₂, ha₂c₂, hb₂c₂, rfl,
            hba₂, hbb₂, hbc₂, hJ₂, hQ₂, hK₂⟩ := h₂face
    apply rankState_eq_same_size_same_ranks
    · -- Both face moves have size 3
      have h1 : a₁ ∉ ({b₁, c₁} : Finset (Fin 9)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨ha₁b₁, ha₁c₁⟩
      have h2 : b₁ ∉ ({c₁} : Finset (Fin 9)) := by simp [hb₁c₁]
      have h3 : a₂ ∉ ({b₂, c₂} : Finset (Fin 9)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨ha₂b₂, ha₂c₂⟩
      have h4 : b₂ ∉ ({c₂} : Finset (Fin 9)) := by simp [hb₂c₂]
      rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
          Finset.card_singleton,
          Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h4,
          Finset.card_singleton]
    · -- Both remove the same ranks {J, Q, K}
      rw [face_val_map s a₁ b₁ c₁ ha₁b₁ ha₁c₁ hb₁c₁ ca₁ cb₁ cc₁ hba₁ hbb₁ hbc₁ hJ₁ hQ₁ hK₁,
          face_val_map s a₂ b₂ c₂ ha₂b₂ ha₂c₂ hb₂c₂ ca₂ cb₂ cc₂ hba₂ hbb₂ hbc₂ hJ₂ hQ₂ hK₂]

/-! ## Main Theorem -/

/-- Helper for the hard direction of `outcome_deterministic`:
    if `s` is winnable and `m` is legal, then `applyMove s m` is winnable.
    Proved by strong induction on `remaining s`. -/
private lemma outcome_deterministic_fwd (s : GameState) (m : Move) (h : IsLegal s m)
    (hwin : Winnable s) : Winnable (applyMove s m) := by
  induction hn : remaining s using Nat.strongRecOn generalizing s m with
  | ind n ih =>
  obtain ⟨moves, hleg, hwin_seq⟩ := hwin
  cases moves with
  | nil =>
    -- s is a win with no moves, but m is legal — contradiction
    simp only [List.foldl_nil] at hwin_seq
    have ⟨hbr, hpr⟩ := (isWin_iff_rankState s).mp hwin_seq
    have hrem : remaining s = 0 := by rw [remaining_eq_rankState, hbr, hpr]; simp
    exact absurd (remaining_applyMove_lt s m h) (by omega)
  | cons m₂ rest =>
    -- Extract m₂ as first legal move and rest as winning sequence for applyMove s m₂
    have hm₂_legal : IsLegal s m₂ := by
      have := hleg ⟨0, Nat.zero_lt_succ _⟩; simp at this; exact this
    have hrest_legal : ∀ i : Fin rest.length,
        IsLegal ((rest.take i.val).foldl applyMove (applyMove s m₂)) (rest.get i) := by
      intro ⟨k, hk⟩
      have := hleg ⟨k + 1, Nat.succ_lt_succ hk⟩
      simp only [List.take_succ_cons, List.foldl_cons, List.get_cons_succ] at this
      exact this
    have hwin_m₂ : Winnable (applyMove s m₂) := ⟨rest, hrest_legal, by simpa using hwin_seq⟩
    by_cases hdisj : Disjoint m m₂
    · -- m and m₂ are disjoint: use commutativity
      have hm₂_after_m : IsLegal (applyMove s m) m₂ :=
        disjoint_preserves_legality s m m₂ h hm₂_legal hdisj
      have hm_after_m₂ : IsLegal (applyMove s m₂) m :=
        disjoint_preserves_legality s m₂ m hm₂_legal h (Disjoint.symm hdisj)
      have hcomm : rankState (applyMove (applyMove s m) m₂) =
                   rankState (applyMove (applyMove s m₂) m) :=
        disjoint_moves_commute s m m₂ h hm₂_legal hdisj
      -- Apply IH to (applyMove s m₂, m): remaining decreases
      have hrem_lt : remaining (applyMove s m₂) < n :=
        hn ▸ remaining_applyMove_lt s m₂ hm₂_legal
      have hT₂ : Winnable (applyMove (applyMove s m₂) m) :=
        ih (remaining (applyMove s m₂)) hrem_lt (applyMove s m₂) m hm_after_m₂ hwin_m₂ rfl
      -- T₁ and T₂ have equal rank-states, so equal winnability
      have hT₁ : Winnable (applyMove (applyMove s m) m₂) :=
        (rankState_determines_outcome _ _ hcomm).mpr hT₂
      -- Extract winning sequence for applyMove s m
      obtain ⟨moves', hleg', hwin'⟩ := hT₁
      exact ⟨m₂ :: moves',
        fun ⟨k, hk⟩ => match k with
          | 0 => hm₂_after_m
          | k + 1 => by
              simp only [List.take_succ_cons, List.foldl_cons, List.get_cons_succ]
              exact hleg' ⟨k, Nat.lt_of_succ_lt_succ hk⟩,
        by simpa using hwin'⟩
    · -- m and m₂ share a slot: use rank preservation
      have hrk_eq : rankState (applyMove s m) = rankState (applyMove s m₂) :=
        shared_slot_rank_preserved s m m₂ h hm₂_legal hdisj
      exact (rankState_determines_outcome _ _ hrk_eq).mpr hwin_m₂

theorem outcome_deterministic (s : GameState) (m : Move)
    (h : IsLegal s m) :
    Winnable (applyMove s m) ↔ Winnable s := by
  constructor
  · -- → direction: prepend m to the winning sequence
    intro ⟨moves, hleg, hwin⟩
    exact ⟨m :: moves,
      fun ⟨k, hk⟩ => match k with
        | 0 => h
        | k + 1 => by
            simp only [List.take_succ_cons, List.foldl_cons, List.get_cons_succ]
            exact hleg ⟨k, Nat.lt_of_succ_lt_succ hk⟩,
      by simpa using hwin⟩
  · -- ← direction: by strong induction (see outcome_deterministic_fwd)
    exact outcome_deterministic_fwd s m h

/-! ## Corollary -/

/-- **Corollary (Confluence).** All legal moves from any state lead to
    equally winnable successors. -/
theorem confluence (s : GameState) (m₁ m₂ : Move)
    (h₁ : IsLegal s m₁) (h₂ : IsLegal s m₂) :
    Winnable (applyMove s m₁) ↔ Winnable (applyMove s m₂) := by
  rw [outcome_deterministic s m₁ h₁, outcome_deterministic s m₂ h₂]

/-- **Corollary (Win Rate is Policy-Independent).** The winnability of a
    shuffle is a property of the shuffle alone: no play policy can win an
    unwinnable shuffle or lose a winnable one. -/
theorem win_rate_well_defined :
    ∀ s : GameState,
    (Winnable s → ∀ m : Move, IsLegal s m → Winnable (applyMove s m)) ∧
    (¬ Winnable s → ∀ m : Move, IsLegal s m → ¬ Winnable (applyMove s m)) := by
  intro s
  constructor
  · intro hw m hm
    rwa [outcome_deterministic s m hm]
  · intro hnw m hm hw
    apply hnw
    rwa [← outcome_deterministic s m hm]

end Elevens
