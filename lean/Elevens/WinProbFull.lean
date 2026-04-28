import Elevens.Confluence
import Std.Data.HashMap

/-!
# Win Probability — Full Elevens Game

Full Elevens (13 ranks, 4 copies each, board size 9) win probability DP.
Proves exact win probabilities for the base game and the flip variant.

## Game Parameters

- 13 ranks: A(0)..K(12), 4 copies each, board size 9
- Complement pairs summing to 11: (0,9),(1,8),(2,7),(3,6),(4,5)
- Face triple: J(10), Q(11), K(12) — removed together
- Flip variant: when stuck, flip top card; if it completes a complement pair, proceed

## Representation

Board and pile are `Array ℕ` of length 13, indexed by rank (0..12).
Array representation avoids closure-chain overhead: each update rebuilds the
13-element array via `List.map + toArray`, giving O(1) per-rank access with no
closure traversal. `native_decide` compiles this to efficient OCaml native code.

## Strategy

Memoization via `Std.HashMap (Array ℕ) ℚ` with a canonical key that
collapses ~23,040× symmetry (5! × 2^5 × 3! from pair/face symmetries).
`native_decide` handles ~462,983 canonical states.
-/

namespace Elevens

/-! ## Types -/

/-- Board state: count of each rank on the board (indices 0..12), length 13. -/
abbrev Board13 := Array ℕ

/-- Pile state: count of each rank remaining in the pile (indices 0..12), length 13. -/
abbrev Pile13  := Array ℕ

/-- Memo table: canonical key → win probability. -/
abbrev FullMemo := Std.HashMap (Array ℕ) ℚ

/-! ## Array helpers

All construction is via `List.finRange 13 |>.map f |>.toArray` to avoid
`Array.set` (which requires a `Fin a.size` proof) and `Array.mkArray`
(unavailable in this Lean version).
-/

/-- Build a 13-element array from a function on ranks. -/
@[inline] def mkArr13 (f : Fin 13 → ℕ) : Array ℕ :=
  (List.finRange 13).map f |>.toArray

/-- Zero array (length 13). -/
def zeroArr13 : Array ℕ := mkArr13 (fun _ => 0)

/-- Decrement rank r by 1. -/
def decR (a : Array ℕ) (r : Fin 13) : Array ℕ :=
  mkArr13 (fun i => if i = r then a[i.val]! - 1 else a[i.val]!)

/-- Increment rank r by 1. -/
def incR (a : Array ℕ) (r : Fin 13) : Array ℕ :=
  mkArr13 (fun i => if i = r then a[i.val]! + 1 else a[i.val]!)

/-- Point-wise add two arrays. -/
def addArr13 (a b : Array ℕ) : Array ℕ :=
  mkArr13 (fun i => a[i.val]! + b[i.val]!)

/-- Point-wise subtract b from a. -/
def subArr13 (a b : Array ℕ) : Array ℕ :=
  mkArr13 (fun i => a[i.val]! - b[i.val]!)

/-- Sum all entries. -/
def arraySum13 (a : Array ℕ) : ℕ := a.foldl (· + ·) 0

/-! ## Rank groups -/

/-- The 5 complement pairs: ranks summing to 11. -/
def elevensPairs : List (Fin 13 × Fin 13) :=
  [(⟨0, by omega⟩, ⟨9, by omega⟩), (⟨1, by omega⟩, ⟨8, by omega⟩),
   (⟨2, by omega⟩, ⟨7, by omega⟩), (⟨3, by omega⟩, ⟨6, by omega⟩),
   (⟨4, by omega⟩, ⟨5, by omega⟩)]

/-- The 3 face ranks: J, Q, K (indices 10, 11, 12). -/
def elevensFaces : List (Fin 13) :=
  [⟨10, by omega⟩, ⟨11, by omega⟩, ⟨12, by omega⟩]

/-! ## Canonical key

Collapses symmetry:
- 5! ways to order the 5 complement pairs
- 2^5 ways to swap within each pair (a↔b)
- 3! ways to order the 3 face ranks
Total: 5! × 2^5 × 3! = 23,040
-/

/-- Lexicographic comparison of two `Array ℕ`. -/
def arrayLeq (a b : Array ℕ) : Bool :=
  let rec go : ℕ → Bool
    | i =>
      if i ≥ a.size then true
      else if i ≥ b.size then false
      else if a[i]! < b[i]! then true
      else if b[i]! < a[i]! then false
      else go (i + 1)
  termination_by i => a.size - i
  go 0

/-- Canonical key for a (board, pile) state as an Array ℕ of length 26.

    Within each complement pair, we put the lex-smaller (board, pile) entry first.
    We use explicit lexicographic comparison on (ℕ × ℕ) because Lean's `≤` on
    product types is componentwise (partial order), not lexicographic (total order). -/
def canonKey13 (board pile : Board13) : Array ℕ :=
  -- Lexicographic total order on (ℕ × ℕ).
  let lexle2 : ℕ × ℕ → ℕ × ℕ → Bool := fun (a1, a2) (b1, b2) =>
    a1 < b1 || (a1 == b1 && a2 ≤ b2)
  -- For each complement pair, build a 4-element array (smaller first).
  let pairSigs : List (Array ℕ) := elevensPairs.map fun (a, b) =>
    let pa := (board[a.val]!, pile[a.val]!)
    let pb := (board[b.val]!, pile[b.val]!)
    if lexle2 pa pb then #[pa.1, pa.2, pb.1, pb.2]
    else                  #[pb.1, pb.2, pa.1, pa.2]
  -- Sort pair sigs (collapses pair-ordering symmetry).
  let sortedPairSigs := pairSigs.mergeSort arrayLeq
  -- For each face rank, build a 2-element array.
  let faceSigs : List (Array ℕ) := elevensFaces.map fun r =>
    #[board[r.val]!, pile[r.val]!]
  -- Sort face sigs (collapses J/Q/K ordering symmetry).
  let sortedFaceSigs := faceSigs.mergeSort arrayLeq
  -- Flatten to a single array of length 26.
  (sortedPairSigs ++ sortedFaceSigs).foldl (· ++ ·) #[]

/-! ## Draw enumeration for 13 ranks -/

/-- Enumerate all ways to draw exactly `k` cards from `pile` (13 ranks).
    Returns list of (draw_array, weight_numerator) pairs.
    Weight denominator is C(sum pile, k). -/
def enumDraws13 (pile : Pile13) (k : ℕ) : List (Array ℕ × ℕ) :=
  let init : List (Array ℕ × ℕ × ℕ) := [(zeroArr13, 1, 0)]
  let extended := (List.finRange 13).foldl (fun partials r =>
    partials.flatMap fun (draw, weight, soFar) =>
      let remaining := k - soFar
      let maxD      := min (pile[r.val]!) remaining
      (List.range (maxD + 1)).map fun d =>
        -- Rebuild draw array with rank r set to d.
        let newDraw : Array ℕ := mkArr13 (fun i => if i = r then d else draw[i.val]!)
        let newWeight := weight * Nat.choose (pile[r.val]!) d
        (newDraw, newWeight, soFar + d))
    init
  (extended.filter fun (_, _, soFar) => soFar = k)
    |>.map fun (draw, weight, _) => (draw, weight)

/-! ## Move detection -/

/-- Find the first legal move on the board, or `none` if stuck.
    Returns `Sum.inl (a, b)` for a numeric complement pair,
    `Sum.inr ()` for the J/Q/K face triple. -/
def findMove13 (board : Board13) : Option (Sum (Fin 13 × Fin 13) Unit) :=
  if let some p := elevensPairs.find? (fun (a, b) =>
      decide (board[a.val]! > 0 ∧ board[b.val]! > 0)) then
    some (Sum.inl p)
  else if elevensFaces.all (fun r => decide (board[r.val]! > 0)) then
    some (Sum.inr ())
  else
    none

/-! ## Fuel-based DP with explicit memo threading -/

/-- Win probability DP for full Elevens.
    `flip = true` enables the flip mechanic for the flip variant.
    Fuel ≥ 52 (total deck size) is sufficient. -/
def winProbFull (flip : Bool) : ℕ → Board13 → Pile13 → FullMemo → FullMemo × ℚ
  | 0, board, pile, memo =>
    (memo, if arraySum13 board = 0 && arraySum13 pile = 0 then 1 else 0)
  | fuel + 1, board, pile, memo =>
    let key := canonKey13 board pile
    -- Check memo cache
    if let some v := memo[key]? then (memo, v)
    else
    let boardTotal := arraySum13 board
    let pileTotal  := arraySum13 pile
    -- Win condition: all cards gone
    if boardTotal = 0 && pileTotal = 0 then
      (memo.insert key 1, 1)
    else
    match findMove13 board with
    | some move =>
      -- Apply the move: remove matched cards from board
      let (clearedBoard, moveSize) : Board13 × ℕ :=
        match move with
        | Sum.inl (a, b) =>
          (decR (decR board a) b, 2)
        | Sum.inr () =>
          (decR (decR (decR board ⟨10, by omega⟩) ⟨11, by omega⟩) ⟨12, by omega⟩, 3)
      -- Draw k = min(moveSize, pileTotal) cards to refill
      let k := min moveSize pileTotal
      let denom := Nat.choose pileTotal k
      if k = 0 then
        -- No cards to draw; recurse directly
        let (memo', v) := winProbFull flip fuel clearedBoard pile memo
        (memo'.insert key v, v)
      else
        let draws := enumDraws13 pile k
        let (memo', prob) := draws.foldl (fun (m : FullMemo × ℚ) (dwNum : Array ℕ × ℕ) =>
          let dw   := dwNum.1
          let wNum := dwNum.2
          let nextBoard : Board13 := addArr13 clearedBoard dw
          let nextPile  : Pile13  := subArr13 pile dw
          let (m', v) := winProbFull flip fuel nextBoard nextPile m.1
          (m', m.2 + (wNum : ℚ) / (denom : ℚ) * v)
        ) (memo, 0)
        (memo'.insert key prob, prob)
    | none =>
      -- No legal move: stuck
      if !flip || pileTotal = 0 then
        -- Base game loss, or flip variant with empty pile
        (memo.insert key 0, 0)
      else
        -- Flip variant: turn over the top card probabilistically.
        -- For each rank r (weight pile[r] / pileTotal):
        --   If r < 10 and its complement (9 - r) is on the board → flip succeeds.
        --   Otherwise → no help.
        -- On success: remove r from pile and complement from board,
        --   then refill 1 slot from the remaining pile.
        let (memo', prob) := (List.finRange 13).foldl
          (fun (state : FullMemo × ℚ) (r : Fin 13) =>
            if pile[r.val]! = 0 then state
            else
              let m   := state.1
              let acc := state.2
              let flipWeight : ℚ := (pile[r.val]! : ℚ) / (pileTotal : ℚ)
              -- Only non-face ranks (r.val < 10) can complete a complement pair
              if r.val < 10 then
                let compIdx : ℕ := 9 - r.val
                have hcomp : compIdx < 13 := by omega
                let comp : Fin 13 := ⟨compIdx, hcomp⟩
                if board[comp.val]! > 0 then
                  -- Flip succeeds: remove flipped card from pile, complement from board
                  let postPile  : Pile13  := decR pile r
                  let postBoard : Board13 := decR board comp
                  let newPileTotal := pileTotal - 1
                  if newPileTotal = 0 then
                    -- Pile exhausted after flip; recurse without refill
                    let (m', v) := winProbFull flip fuel postBoard postPile m
                    (m', acc + flipWeight * v)
                  else
                    -- Refill 1 slot: draw 1 card from postPile
                    let (m', refillProb) := (List.finRange 13).foldl
                      (fun (rs : FullMemo × ℚ) (rr : Fin 13) =>
                        if postPile[rr.val]! = 0 then rs
                        else
                          let refillWeight : ℚ := (postPile[rr.val]! : ℚ) / (newPileTotal : ℚ)
                          let nextPile  : Pile13  := decR postPile rr
                          let nextBoard : Board13 := incR postBoard rr
                          let (rm, v) := winProbFull flip fuel nextBoard nextPile rs.1
                          (rm, rs.2 + refillWeight * v))
                      (m, 0)
                    (m', acc + flipWeight * refillProb)
                else (m, acc)  -- complement not on board
              else (m, acc)    -- face card: flip doesn't help
          ) (memo, 0)
        (memo'.insert key prob, prob)

/-! ## Initial deal and win rate -/

/-- Full deck: 4 copies of each of 13 ranks. -/
def fullDeck13 : Array ℕ := mkArr13 (fun _ => 4)

/-- All initial deals: draw 9 cards from 52, with hypergeometric weights.
    Returns list of (board, pile, probability). -/
def elevensInitialDeal : List (Board13 × Pile13 × ℚ) :=
  let denom : ℕ := Nat.choose 52 9
  (enumDraws13 fullDeck13 9).map fun (dwNum : Array ℕ × ℕ) =>
    let dw   := dwNum.1
    let wNum := dwNum.2
    let board : Board13 := dw
    let pile  : Pile13  := subArr13 fullDeck13 dw
    (board, pile, (wNum : ℚ) / (denom : ℚ))

/-- Compute win rate by summing over all initial deals. -/
def elevensWinRateCompute (flip : Bool) : ℚ :=
  let initDist := elevensInitialDeal
  (initDist.foldl (fun (state : FullMemo × ℚ) (bpp : Board13 × Pile13 × ℚ) =>
    let board := bpp.1
    let pile  := bpp.2.1
    let prob  := bpp.2.2
    let (memo', v) := winProbFull flip 52 board pile state.1
    (memo', state.2 + prob * v)
  ) ((∅ : Std.HashMap (Array ℕ) ℚ), 0)).2

/-- Win rate for base Elevens (no flip). -/
def elevensWinRate : ℚ := elevensWinRateCompute false

/-- Win rate for Elevens with flip mechanic. -/
def elevensFlipWinRate : ℚ := elevensWinRateCompute true

/-! ## Main theorems -/

/-- **Base Elevens win probability.**
    Proved by native_decide (OCaml native code, memoized DP over ~462,983 states). -/
theorem elevensWinRate_eq :
    elevensWinRate =
      135528433265058017167416678875877619324826 /
      1267970709742491186578322321454365697265625 := by
  native_decide

/-- **Flip-variant win probability.**
    Proved by native_decide. -/
theorem elevensFlipWinRate_eq :
    elevensFlipWinRate =
      8148818506107124832421641049420090762431 /
      40902280959435199567042655530785990234375 := by
  native_decide

end Elevens
