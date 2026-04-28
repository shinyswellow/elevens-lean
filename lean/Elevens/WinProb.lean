import Elevens.Confluence

/-!
# Win Probability — POC Spike

Spike for the Lean DP verification. Formalises a standalone POC game (6 ranks,
2 copies each, board size 4, pairs summing to 7) and proves the win probability
equals 3217/5775.

## Design

- `PocState` tracks rank-count vectors: `board : Fin 6 → ℕ` and `pile : Fin 6 → ℕ`.
  Suits and board slot positions are irrelevant (proved in Confluence.lean).

- `winProbPoc` is defined by structural recursion on a fuel parameter.
  This makes it computable without a separate termination proof.

- `poc_win_prob` is closed by `native_decide`.

## STATUS 2026-04-25

  lake build passes with no sorrys. All lemmas fully proved:
  - enumDraws_draw_le: outputs of enumDraws satisfy draw r ≤ pile r pointwise
    (proved via foldlStep induction over ranks)
  - winProbPocFuel_adequate: fuel monotonicity (uses enumDraws_draw_le for sum cancel)
  - winProbPoc_eq_recurrence: the DP recurrence equation holds for all reachable states

  Key obstacles for L1+L2 non-spike:
  1. Bridging PocState and GameState formalisms (different deck sizes/rules).
  2. Well-founded recursion proof for winProbPoc without fuel.
  3. Formal proof that the hypergeometric weighting is correct.
-/

namespace Elevens

/-! ## POC game types -/

/-- A POC state: rank-count vectors (each rank 0–5, each count 0–2). -/
structure PocState where
  board : Fin 6 → ℕ
  pile  : Fin 6 → ℕ
  deriving DecidableEq

/-- The complement pairs: (0,5), (1,4), (2,3). -/
def pocPairs : List (Fin 6 × Fin 6) :=
  [(0, 5), (1, 4), (2, 3)]

/-- Find the first legal pair move. -/
def findPocMove (board : Fin 6 → ℕ) : Option (Fin 6 × Fin 6) :=
  pocPairs.find? fun (a, b) => decide (board a > 0 ∧ board b > 0)

/-! ## Draw enumeration

We enumerate all multisets of size k drawable from a pile (rank-count vector)
as a fold over ranks 0..5. Each partial solution is a pair (draw_vector, weight_numerator)
where weight_numerator is the product of C(pile[r], draw[r]) over ranks seen so far.
The denominator is C(pile_total, k), computed separately. -/

/-- Enumerate all ways to draw exactly `k` cards from `pile`.
    Returns a list of (draw_vector, weight_numerator) pairs.
    The weight denominator is C(sum pile, k). -/
def enumDraws (pile : Fin 6 → ℕ) (k : ℕ) : List ((Fin 6 → ℕ) × ℕ) :=
  -- Build via fold over ranks: maintain list of (partial_draw, partial_weight, drawn_so_far)
  let init : List ((Fin 6 → ℕ) × ℕ × ℕ) := [(fun _ => 0, 1, 0)]
  let extended := (List.finRange 6).foldl (fun partials r =>
    partials.flatMap fun (draw, weight, soFar) =>
      -- How many of rank r can we draw?
      -- We need exactly k - soFar more from ranks r..5.
      -- Minimum: max(0, (k - soFar) - pile_remaining_after_r)
      -- Maximum: min(pile[r], k - soFar)
      let remaining := k - soFar  -- cards still needed
      let pileRemaining := pile r  -- pile[r] available
      let maxD := min pileRemaining remaining
      (List.range (maxD + 1)).map fun d =>
        let newDraw : Fin 6 → ℕ := fun r' => if r' = r then d else draw r'
        let newWeight := weight * Nat.choose (pile r) d
        (newDraw, newWeight, soFar + d))
    init
  -- Filter to draws that sum to exactly k
  (extended.filter fun (draw, _, soFar) => soFar = k)
    |>.map fun (draw, weight, _) => (draw, weight)

/-! ## Win probability DP -/

/-- Computable win probability, fuel-bounded.
    Fuel = 12 suffices since pocRemaining ≤ 12 for all reachable POC states. -/
def winProbPocFuel : ℕ → PocState → ℚ
  | 0, s =>
    if Finset.univ.sum s.board = 0 ∧ Finset.univ.sum s.pile = 0 then 1 else 0
  | fuel + 1, s =>
    let boardTotal := Finset.univ.sum s.board
    let pileTotal  := Finset.univ.sum s.pile
    if boardTotal = 0 ∧ pileTotal = 0 then 1
    else match findPocMove s.board with
    | none => 0
    | some (a, b) =>
        -- Remove pair from board
        let board₁ : Fin 6 → ℕ := fun r =>
          if r = a then s.board r - 1
          else if r = b then s.board r - 1
          else s.board r
        -- Draw min(2, pileTotal) cards from pile
        let k := min 2 pileTotal
        let denom := Nat.choose pileTotal k
        if k = 0 then
          winProbPocFuel fuel ⟨board₁, s.pile⟩
        else
          (enumDraws s.pile k).foldl (fun acc (draw, weightNum) =>
            let nextBoard : Fin 6 → ℕ := fun r => board₁ r + draw r
            let nextPile  : Fin 6 → ℕ := fun r => s.pile r - draw r
            acc + (weightNum : ℚ) / (denom : ℚ) *
                  winProbPocFuel fuel ⟨nextBoard, nextPile⟩
          ) 0

/-- Win probability with fuel 12 (total POC deck size). -/
def winProbPoc (s : PocState) : ℚ :=
  winProbPocFuel 12 s

/-! ## Initial state distribution -/

/-- Full POC deck: 2 copies of each of 6 ranks. -/
def pocFullDeck : Fin 6 → ℕ := fun _ => 2

/-- The initial deal distribution: all ways to draw 4 cards from the full deck,
    each weighted by the multivariate hypergeometric probability. -/
def pocInitialDist : List (PocState × ℚ) :=
  let denom : ℕ := Nat.choose 12 4  -- C(12,4) = 495
  (enumDraws pocFullDeck 4).map fun (draw, weightNum) =>
    let board := draw
    let pile : Fin 6 → ℕ := fun r => pocFullDeck r - draw r
    (⟨board, pile⟩, (weightNum : ℚ) / (denom : ℚ))

/-- Overall win probability: weighted sum over initial deal distribution. -/
def pocWinRate : ℚ :=
  pocInitialDist.foldl (fun acc (s, prob) => acc + prob * winProbPoc s) 0

/-! ## Main theorem -/

/-- **Validation.** The POC game win probability is 3217/5775.

    Closed by native_decide: the computation is a finite rational arithmetic
    evaluation over 90 initial states with fuel-12 DP. -/
theorem poc_win_prob : pocWinRate = 3217 / 5775 := by
  native_decide

/-! ## Fuel-adequacy lemmas -/

/-- Extract pair condition from findPocMove result. -/
private lemma findPocMove_pos {board : Fin 6 → ℕ} {a b : Fin 6}
    (hm : findPocMove board = some (a, b)) :
    board a > 0 ∧ board b > 0 := by
  unfold findPocMove at hm
  have := List.find?_some hm
  simp only [decide_eq_true_eq] at this
  exact this

/-- All pairs in pocPairs have distinct components. -/
private lemma findPocMove_ne {board : Fin 6 → ℕ} {a b : Fin 6}
    (hm : findPocMove board = some (a, b)) : a ≠ b := by
  unfold findPocMove at hm
  have hmem := List.mem_of_find?_eq_some hm
  simp only [pocPairs, List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with h | h | h <;> simp_all <;> decide

/-- Removing pair (a, b) from board reduces the sum by exactly 2.

    Proof uses Finset.add_sum_erase to split the sum at a and b:
    sum f = (board a - 1) + (board b - 1) + sum_{rest} board
          = board a + board b + sum_{rest} board - 2
          = sum board - 2. -/
private lemma board_sum_sub_pair {board : Fin 6 → ℕ} {a b : Fin 6}
    (ha : board a ≥ 1) (hb : board b ≥ 1) (hab : a ≠ b) :
    Finset.univ.sum (fun r : Fin 6 =>
      if r = a then board r - 1
      else if r = b then board r - 1
      else board r) + 2 = Finset.univ.sum board := by
  have ha_mem : a ∈ (Finset.univ : Finset (Fin 6)) := Finset.mem_univ _
  have hb_mem : b ∈ (Finset.univ : Finset (Fin 6)) := Finset.mem_univ _
  have hb_erase : b ∈ (Finset.univ : Finset (Fin 6)).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, hb_mem⟩
  set f : Fin 6 → ℕ := fun r =>
    if r = a then board r - 1 else if r = b then board r - 1 else board r
  set g : Fin 6 → ℕ := fun r => if r = b then board r - 1 else board r
  -- Split sum f at a
  have hfa : f a = board a - 1 := by simp [f]
  have sum_f_split : Finset.univ.sum f = f a + (Finset.univ.erase a).sum f :=
    (Finset.add_sum_erase _ _ ha_mem).symm
  -- On erase a, f = g (since r ≠ a)
  have fg_eq : (Finset.univ.erase a).sum f = (Finset.univ.erase a).sum g := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.mem_erase] at hr
    simp [f, g, hr.1]
  -- Split sum g at b (within erase a)
  have hgb : g b = board b - 1 := by simp [g]
  have sum_g_split : (Finset.univ.erase a).sum g = g b + ((Finset.univ.erase a).erase b).sum g :=
    (Finset.add_sum_erase _ _ hb_erase).symm
  -- On (erase a).erase b, g = board
  have g_eq_board : ((Finset.univ.erase a).erase b).sum g =
      ((Finset.univ.erase a).erase b).sum board := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.mem_erase] at hr
    simp [g, hr.1]
  -- Split sum board at a and b similarly
  have sum_board_a : Finset.univ.sum board = board a + (Finset.univ.erase a).sum board :=
    (Finset.add_sum_erase _ _ ha_mem).symm
  have sum_board_b : (Finset.univ.erase a).sum board =
      board b + ((Finset.univ.erase a).erase b).sum board :=
    (Finset.add_sum_erase _ _ hb_erase).symm
  -- Assemble: sum f + 2 = sum board
  rw [sum_f_split, hfa, fg_eq, sum_g_split, hgb, g_eq_board,
      sum_board_a, sum_board_b]
  omega

/-- Helper: foldl over draw list is the same when inner DP values agree for members. -/
private lemma foldl_winProb_congr
    (draws : List ((Fin 6 → ℕ) × ℕ)) (denom : ℕ)
    (board₁ pile : Fin 6 → ℕ)
    (f g : PocState → ℚ)
    (hfg : ∀ draw wn, (draw, wn) ∈ draws →
      f ⟨fun r => board₁ r + draw r, fun r => pile r - draw r⟩ =
      g ⟨fun r => board₁ r + draw r, fun r => pile r - draw r⟩) :
    draws.foldl (fun acc (draw, wn) =>
        acc + (wn : ℚ) / (denom : ℚ) *
          f ⟨fun r => board₁ r + draw r, fun r => pile r - draw r⟩) 0 =
    draws.foldl (fun acc (draw, wn) =>
        acc + (wn : ℚ) / (denom : ℚ) *
          g ⟨fun r => board₁ r + draw r, fun r => pile r - draw r⟩) 0 := by
  suffices h : ∀ acc : ℚ, ∀ subdraws : List ((Fin 6 → ℕ) × ℕ),
      (∀ dw ∈ subdraws, dw ∈ draws) →
      subdraws.foldl (fun a (dw : (Fin 6 → ℕ) × ℕ) =>
          a + (dw.2 : ℚ) / (denom : ℚ) *
            f ⟨fun r => board₁ r + dw.1 r, fun r => pile r - dw.1 r⟩) acc =
      subdraws.foldl (fun a (dw : (Fin 6 → ℕ) × ℕ) =>
          a + (dw.2 : ℚ) / (denom : ℚ) *
            g ⟨fun r => board₁ r + dw.1 r, fun r => pile r - dw.1 r⟩) acc by
    exact h 0 draws (fun dw h => h)
  intro acc subdraws hsub
  induction subdraws generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨hdraw, hwn⟩ := hd
    simp only [List.foldl_cons]
    have hhdmem : (hdraw, hwn) ∈ draws := hsub (hdraw, hwn) List.mem_cons_self
    have hfgeq := hfg hdraw hwn hhdmem
    rw [hfgeq]
    exact ih _ (fun dw h => hsub dw (List.mem_cons_of_mem _ h))

/-! ## Draw validity: outputs of enumDraws satisfy draw r ≤ pile r pointwise -/

-- Internal fold step mirroring enumDraws construction
private def foldlStep (pile : Fin 6 → ℕ) (k : ℕ)
    (partials : List ((Fin 6 → ℕ) × ℕ × ℕ)) (rc : Fin 6) :
    List ((Fin 6 → ℕ) × ℕ × ℕ) :=
  partials.flatMap fun (draw, weight, soFar) =>
    (List.range (min (pile rc) (k - soFar) + 1)).map fun d =>
      (fun ri => if ri = rc then d else draw ri,
       weight * Nat.choose (pile rc) d, soFar + d)

private lemma foldlStep_le (pile : Fin 6 → ℕ) (k : ℕ) (rc : Fin 6)
    (init : List ((Fin 6 → ℕ) × ℕ × ℕ))
    (draw : Fin 6 → ℕ) (wn soFar : ℕ)
    (hmem : (draw, wn, soFar) ∈ foldlStep pile k init rc) :
    draw rc ≤ pile rc := by
  simp only [foldlStep, List.mem_flatMap, List.mem_map, List.mem_range] at hmem
  obtain ⟨⟨draw0, wn0, soFar0⟩, -, d, hd, heq⟩ := hmem
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hdraw, -, -⟩ := heq
  rw [← hdraw]; simp only [ite_true]; omega

private lemma foldlStep_preserves (pile : Fin 6 → ℕ) (k : ℕ) (r rc : Fin 6) (hne : r ≠ rc)
    (init : List ((Fin 6 → ℕ) × ℕ × ℕ))
    (draw : Fin 6 → ℕ) (wn soFar : ℕ)
    (hmem : (draw, wn, soFar) ∈ foldlStep pile k init rc) :
    ∃ draw0 wn0 soFar0, (draw0, wn0, soFar0) ∈ init ∧ draw r = draw0 r := by
  simp only [foldlStep, List.mem_flatMap, List.mem_map, List.mem_range] at hmem
  obtain ⟨⟨draw0, wn0, soFar0⟩, hin0, d, -, heq⟩ := hmem
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hdraw, -, -⟩ := heq
  exact ⟨draw0, wn0, soFar0, hin0, by rw [← hdraw]; simp [hne]⟩

private lemma foldl_preserves (pile : Fin 6 → ℕ) (k : ℕ) (r : Fin 6)
    (rs : List (Fin 6)) (hr : r ∉ rs)
    (init : List ((Fin 6 → ℕ) × ℕ × ℕ))
    (draw : Fin 6 → ℕ) (wn soFar : ℕ)
    (hmem : (draw, wn, soFar) ∈ rs.foldl (foldlStep pile k) init) :
    ∃ draw0 wn0 soFar0, (draw0, wn0, soFar0) ∈ init ∧ draw r = draw0 r := by
  induction rs generalizing init draw wn soFar with
  | nil => exact ⟨draw, wn, soFar, hmem, rfl⟩
  | cons rc rest ih =>
    simp only [List.mem_cons, not_or] at hr
    simp only [List.foldl_cons] at hmem
    obtain ⟨d1, w1, s1, hm1, heq1⟩ := ih hr.2 _ _ _ _ hmem
    obtain ⟨d0, w0, s0, h0, heq0⟩ := foldlStep_preserves pile k r rc hr.1 _ _ _ _ hm1
    exact ⟨d0, w0, s0, h0, by rw [heq1, heq0]⟩

private lemma foldl_all_le (pile : Fin 6 → ℕ) (k : ℕ)
    (rs : List (Fin 6)) (hnodup : rs.Nodup)
    (init : List ((Fin 6 → ℕ) × ℕ × ℕ))
    (h_init_zero : ∀ draw wn soFar, (draw, wn, soFar) ∈ init →
      ∀ r0 ∈ rs, draw r0 = 0)
    (draw : Fin 6 → ℕ) (wn soFar : ℕ)
    (hmem : (draw, wn, soFar) ∈ rs.foldl (foldlStep pile k) init)
    (r : Fin 6) (hr : r ∈ rs) : draw r ≤ pile r := by
  induction rs generalizing init draw wn soFar with
  | nil => simp at hr
  | cons head tail ihtail =>
    simp only [List.nodup_cons] at hnodup
    obtain ⟨hhead_not_tail, hnodup_tail⟩ := hnodup
    simp only [List.mem_cons] at hr
    simp only [List.foldl_cons] at hmem
    rcases hr with rfl | hr_tail
    · obtain ⟨d1, w1, s1, hm1, heq1⟩ :=
        foldl_preserves pile k r tail hhead_not_tail _ _ _ _ hmem
      rw [heq1]
      exact foldlStep_le pile k r init d1 w1 s1 hm1
    · apply ihtail hnodup_tail (foldlStep pile k init head) _ draw wn soFar hmem hr_tail
      intro d2 w2 s2 hm2 r0 hr0_tail
      have hne : r0 ≠ head := fun h => hhead_not_tail (h ▸ hr0_tail)
      obtain ⟨d3, w3, s3, h3, heq3⟩ :=
        foldlStep_preserves pile k r0 head hne _ _ _ _ hm2
      rw [heq3]
      exact h_init_zero d3 w3 s3 h3 r0 (List.mem_cons_of_mem _ hr0_tail)

/-- All draw vectors produced by enumDraws satisfy draw r ≤ pile r pointwise. -/
private lemma enumDraws_draw_le (pile : Fin 6 → ℕ) (k : ℕ)
    (draw : Fin 6 → ℕ) (wn : ℕ)
    (hmem : (draw, wn) ∈ enumDraws pile k) (r : Fin 6) : draw r ≤ pile r := by
  have hmem2 : ∃ soFar, (draw, wn, soFar) ∈
      (List.finRange 6).foldl (foldlStep pile k) [(fun _ => 0, 1, 0)] := by
    simp only [enumDraws, List.mem_map, List.mem_filter] at hmem
    obtain ⟨⟨d2, w2, s2⟩, ⟨hm2, -⟩, heq2⟩ := hmem
    simp only [Prod.mk.injEq] at heq2
    obtain ⟨hd2, hw2⟩ := heq2
    -- hm2 : (d2, w2, s2) ∈ foldl over ranks (enumDraws internals = foldlStep)
    refine ⟨s2, ?_⟩
    -- convert to foldlStep form, then substitute d2 = draw and w2 = wn
    suffices h : (d2, w2, s2) ∈ (List.finRange 6).foldl (foldlStep pile k) [(fun _ => 0, 1, 0)] by
      rwa [hd2, hw2] at h
    convert hm2 using 2
  obtain ⟨soFar, hmem3⟩ := hmem2
  apply foldl_all_le pile k (List.finRange 6) (List.nodup_finRange 6)
    [(fun _ => 0, 1, 0)]
    (by intro d _ _ hd r0 _
        simp only [List.mem_singleton] at hd
        simp only [Prod.mk.injEq] at hd
        obtain ⟨hd2, -, -⟩ := hd
        simp [hd2])
    draw wn soFar hmem3 r (List.mem_finRange r)

/-- Key fuel-adequacy: if remaining ≤ k, then winProbPocFuel k = winProbPocFuel (k+1).

    Proof by strong induction on k (i.e., on remaining card count). -/
private lemma winProbPocFuel_adequate :
    ∀ (k : ℕ) (s : PocState),
    Finset.univ.sum s.board + Finset.univ.sum s.pile ≤ k →
    winProbPocFuel k s = winProbPocFuel (k + 1) s := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s h
    match k with
    | 0 =>
      -- remaining = 0 means both sums are 0
      have hb : Finset.univ.sum s.board = 0 := by omega
      have hp : Finset.univ.sum s.pile = 0 := by omega
      show (if Finset.univ.sum s.board = 0 ∧ Finset.univ.sum s.pile = 0 then (1 : ℚ) else 0) =
           winProbPocFuel 1 s
      simp only [hb, hp, and_self, ite_true]
      simp [winProbPocFuel, hb, hp]
    | n + 1 =>
      -- Show winProbPocFuel (n+1) s = winProbPocFuel (n+2) s
      show winProbPocFuel (n + 1) s = winProbPocFuel (n + 1 + 1) s
      unfold winProbPocFuel
      by_cases hwin : Finset.univ.sum s.board = 0 ∧ Finset.univ.sum s.pile = 0
      · simp [hwin]
      · simp only [hwin, ite_false]
        rcases hm : findPocMove s.board with _ | ⟨a, b⟩
        · rfl
        · -- Recursive case
          have hab := findPocMove_pos hm
          have hab_ne := findPocMove_ne hm
          -- After removing pair, board sum decreases by 2
          have hboard₁_sum :
              Finset.univ.sum (fun r : Fin 6 =>
                if r = a then s.board r - 1 else if r = b then s.board r - 1
                else s.board r) + 2 = Finset.univ.sum s.board :=
            board_sum_sub_pair hab.1 hab.2 hab_ne
          -- board₁ sum + pile sum ≤ n
          have hrem_board₁ :
              Finset.univ.sum (fun r : Fin 6 =>
                if r = a then s.board r - 1 else if r = b then s.board r - 1 else s.board r) +
              Finset.univ.sum s.pile ≤ n := by omega
          split_ifs with hk0
          · -- k_draw = 0: single recursive call, apply IH
            exact ih n (Nat.lt_succ_self n) _ hrem_board₁
          · -- k_draw > 0: apply foldl congruence
            apply foldl_winProb_congr _ _ _ s.pile
              (fun ns => winProbPocFuel n ns)
              (fun ns => winProbPocFuel (n + 1) ns)
            intro draw wn hmem_draw
            apply ih n (Nat.lt_succ_self n)
            -- sum nextBoard + sum nextPile = sum board₁_expr + sum s.pile ≤ n
            -- where board₁_expr is fun r => if r = a then ... else ...
            -- because draws from enumDraws satisfy draw r ≤ s.pile r
            have hdraw_le : ∀ r : Fin 6, draw r ≤ s.pile r :=
              fun r => enumDraws_draw_le s.pile _ draw wn hmem_draw r
            have hle : Finset.univ.sum draw ≤ Finset.univ.sum s.pile :=
              Finset.sum_le_sum (fun r _ => hdraw_le r)
            -- sum nextBoard + sum nextPile
            --   = sum (board₁_expr + draw) + sum (pile - draw)
            --   = (sum board₁_expr + sum draw) + (sum pile - sum draw)
            --   = sum board₁_expr + sum pile ≤ n
            have hadd : Finset.univ.sum (fun r : Fin 6 =>
                  (if r = a then s.board r - 1 else if r = b then s.board r - 1 else s.board r) +
                  draw r) =
                Finset.univ.sum (fun r : Fin 6 =>
                  if r = a then s.board r - 1 else if r = b then s.board r - 1 else s.board r) +
                Finset.univ.sum draw := Finset.sum_add_distrib
            have hsub : Finset.univ.sum (fun r : Fin 6 => s.pile r - draw r) =
                Finset.univ.sum s.pile - Finset.univ.sum draw :=
              Finset.sum_tsub_distrib Finset.univ (fun r _ => hdraw_le r)
            rw [hadd, hsub]
            omega

/-- Monotone fuel: remaining ≤ n ≤ m implies fuel-n and fuel-m agree. -/
private lemma winProbPocFuel_stable {n m : ℕ} (hnm : n ≤ m) (s : PocState)
    (h : Finset.univ.sum s.board + Finset.univ.sum s.pile ≤ n) :
    winProbPocFuel n s = winProbPocFuel m s := by
  induction hnm with
  | refl => rfl
  | step hle ih =>
    rw [ih]
    exact winProbPocFuel_adequate _ s (le_trans h hle)

/-! ## Recurrence (L1+L2 target) -/

/-- **L1.** `winProbPoc` satisfies its defining recurrence equation,
    for states with total card count ≤ 12 (all reachable POC states).

    Proof: unfold winProbPoc = winProbPocFuel 12; the body calls winProbPocFuel 11
    on next states. Use fuel-stability (proved via fuel-adequacy lemma) to show
    fuel-11 = fuel-12 on those states. -/
theorem winProbPoc_eq_recurrence (s : PocState)
    (hrem : Finset.univ.sum s.board + Finset.univ.sum s.pile ≤ 12) :
    winProbPoc s =
      if Finset.univ.sum s.board = 0 ∧ Finset.univ.sum s.pile = 0 then 1
      else match findPocMove s.board with
           | none => 0
           | some (a, b) =>
               let board₁ : Fin 6 → ℕ := fun r =>
                 if r = a then s.board r - 1
                 else if r = b then s.board r - 1
                 else s.board r
               let pileTotal := Finset.univ.sum s.pile
               let k := min 2 pileTotal
               let denom := Nat.choose pileTotal k
               if k = 0 then winProbPoc ⟨board₁, s.pile⟩
               else
                 (enumDraws s.pile k).foldl (fun acc (draw, weightNum) =>
                   let nextBoard : Fin 6 → ℕ := fun r => board₁ r + draw r
                   let nextPile  : Fin 6 → ℕ := fun r => s.pile r - draw r
                   acc + (weightNum : ℚ) / (denom : ℚ) * winProbPoc ⟨nextBoard, nextPile⟩
                 ) 0 := by
  show winProbPocFuel 12 s = _
  unfold winProbPocFuel
  by_cases hwin : Finset.univ.sum s.board = 0 ∧ Finset.univ.sum s.pile = 0
  · simp [hwin]
  · simp only [hwin, ite_false]
    rcases hm : findPocMove s.board with _ | ⟨a, b⟩
    · rfl
    · -- Recursive case: LHS has fuel 11, RHS has fuel 12
      have hab := findPocMove_pos hm
      have hab_ne := findPocMove_ne hm
      have hboard₁_sum :
          Finset.univ.sum (fun r : Fin 6 =>
            if r = a then s.board r - 1 else if r = b then s.board r - 1
            else s.board r) + 2 = Finset.univ.sum s.board :=
        board_sum_sub_pair hab.1 hab.2 hab_ne
      -- board₁ sum + pile sum ≤ 11
      have hrem_board₁ :
          Finset.univ.sum (fun r : Fin 6 =>
            if r = a then s.board r - 1 else if r = b then s.board r - 1 else s.board r) +
          Finset.univ.sum s.pile ≤ 11 := by omega
      split_ifs with hk0
      · -- k_draw = 0: show winProbPocFuel 11 nextState = winProbPocFuel 12 nextState
        show winProbPocFuel 11 _ = winProbPocFuel 12 _
        exact winProbPocFuel_stable (by norm_num) _ hrem_board₁
      · -- k_draw > 0: show foldl with fuel 11 = foldl with fuel 12 (= winProbPoc)
        apply foldl_winProb_congr _ _ _ s.pile
          (fun ns => winProbPocFuel 11 ns)
          (fun ns => winProbPocFuel 12 ns)
        intro draw wn hmem_draw
        show winProbPocFuel 11 _ = winProbPocFuel 12 _
        apply winProbPocFuel_stable (by norm_num)
        -- Need: sum nextBoard + sum nextPile ≤ 11
        have hdraw_le : ∀ r : Fin 6, draw r ≤ s.pile r :=
          fun r => enumDraws_draw_le s.pile _ draw wn hmem_draw r
        have hle : Finset.univ.sum draw ≤ Finset.univ.sum s.pile :=
          Finset.sum_le_sum (fun r _ => hdraw_le r)
        have hadd : Finset.univ.sum (fun r : Fin 6 =>
              (if r = a then s.board r - 1 else if r = b then s.board r - 1 else s.board r) +
              draw r) =
            Finset.univ.sum (fun r : Fin 6 =>
              if r = a then s.board r - 1 else if r = b then s.board r - 1 else s.board r) +
            Finset.univ.sum draw := Finset.sum_add_distrib
        have hsub : Finset.univ.sum (fun r : Fin 6 => s.pile r - draw r) =
            Finset.univ.sum s.pile - Finset.univ.sum draw :=
          Finset.sum_tsub_distrib Finset.univ (fun r _ => hdraw_le r)
        rw [hadd, hsub]
        omega

end Elevens
