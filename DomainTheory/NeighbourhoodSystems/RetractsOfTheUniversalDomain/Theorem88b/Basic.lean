module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.P0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.posnegList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_involutive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_primrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.P0_X

@[expose] public section

/-!
# Theorem 8.8(b), Part 6 — the effective back-and-forth construction

`Theorem88.lean`/`Theorem88a.lean` build Scott's back-and-forth construction generically over an
abstract splitting operation `split` satisfying `SplitSpec`; Part 5 (`DAtomDecidable.lean`) shows
`D`-atom emptiness is recursively decidable for any `ComputablePresentation P` of `D`. This file
assembles the **effective** instantiation: a computable splitting operation `splitEff`, built from
`DAtom_recDecidable` (deciding which side of a `D`-side split is non-empty) and `SplitU.lean`'s
`splitULeft`/`splitURight` (deterministically splitting the matching `U`-side neighbourhood).

## Part 6b: re-pointing `P`'s enumeration at index `0`

`Theorem88a.lean`'s apparatus (`Yidx`, `DprimeU`, `domainIso`) is stated for an arbitrary
enumeration `e : ℕ → Set α` with `e 0 = D.master` (Scott's convention `X₀ = Δ`, needed for
`Yseq_zero_eq_master`). An arbitrary `ComputablePresentation P` need not have `P.masterIdx = 0`, so
we re-point it: `eIdx` swaps `0` and `P.masterIdx` (a primitive-recursive involution), and
`P.reindexInvolutive eIdx …` (Definition71.lean) transports the *entire* computable presentation
along this swap in one step — giving a new presentation `P₀` with `P₀.X 0 = D.master` for free,
with no need to redo any of Part 5's `DAtom` apparatus (it applies to `P₀` exactly as it did to
`P`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






/-- **`e := P₀.X`, Scott's re-enumeration with `e 0 = D.master`.** -/
noncomputable abbrev e : ℕ → Set α := (P0 P).X

/-! ## Part 6c: `genAtom (idxSet e)` emptiness is decidable

`Theorem88.lean`'s `genAtom` tracks the depth-`n` atom for a sign sequence `δ` as a *set*, built by
an `if δ i then Z i else M \ Z i` intersection at each step. `DAtomDecidable.lean`'s `DAtom`, by
contrast, tracks the *same kind* of atom (for `Z := idxSet Q.X`, `M := Set.univ`) as two explicit
`List ℕ` accumulators (`pos`/`neg`) — the very data a primitive-recursive realization needs to
carry. `posnegList` extracts these accumulators from `δ` by mirroring `genAtom`'s own recursion
step-for-step, so `genAtom_eq_DAtom` (below) is a one-line induction, not a `List.range`/`filter`
reindexing exercise. -/


@[simp] theorem posnegList_zero (δ : ℕ → Bool) : posnegList δ 0 = ([], []) := rfl

theorem posnegList_succ_true {δ : ℕ → Bool} {n : ℕ} (h : δ n = true) :
    posnegList δ (n + 1) = ((posnegList δ n).1 ++ [n], (posnegList δ n).2) := by
  show (if δ n then _ else _) = _
  simp [h]

theorem posnegList_succ_false {δ : ℕ → Bool} {n : ℕ} (h : δ n = false) :
    posnegList δ (n + 1) = ((posnegList δ n).1, (posnegList δ n).2 ++ [n]) := by
  show (if δ n then _ else _) = _
  simp [h]

/-- `IPos` splits across list append (order/multiplicity are irrelevant to membership). -/
theorem IPos_append {E : NeighborhoodSystem α} (Q : ComputablePresentation E) (l1 l2 : List ℕ) :
    IPos Q (l1 ++ l2) = IPos Q l1 ∩ IPos Q l2 := by
  induction l1 with
  | nil => simp [IPos_nil]
  | cons a l ih => rw [List.cons_append, IPos_cons, IPos_cons, ih, Set.inter_assoc]

/-- The negative part of `DAtom` splits across list append. -/
theorem negPart_append {E : NeighborhoodSystem α} (Q : ComputablePresentation E)
    (n1 n2 : List ℕ) :
    {m : ℕ | ∀ j ∈ (n1 ++ n2), m ∉ idxSet Q.X j} =
      {m | ∀ j ∈ n1, m ∉ idxSet Q.X j} ∩ {m | ∀ j ∈ n2, m ∉ idxSet Q.X j} := by
  ext m
  simp only [Set.mem_ofPred_eq, List.forall_mem_append, Set.mem_inter_iff]

/-- **`genAtom` reindexed via `idxSet e` matches `DAtom (P0 P)` at the `posnegList`
accumulator.** The heart of Part 6c: since `(P0 P).X = e P`, this is exactly the fact that a
`D`-side atom (Boolean-sequence style) and its `(pos, neg)`-list-style description agree. -/
theorem genAtom_eq_DAtom (δ : ℕ → Bool) :
    ∀ n, genAtom (idxSet (e P)) Set.univ δ n =
      DAtom (P0 P) (posnegList δ n).1 (posnegList δ n).2 := by
  intro n
  induction n with
  | zero => simp [genAtom, DAtom, IPos_nil]
  | succ n ih =>
    rcases Bool.eq_false_or_eq_true (δ n) with h | h
    · have hstep : genAtom (idxSet (e P)) Set.univ δ (n + 1) =
          genAtom (idxSet (e P)) Set.univ δ n ∩ idxSet (e P) n := by
        show genAtom (idxSet (e P)) Set.univ δ n ∩
          (if δ n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [h]
      rw [hstep, posnegList_succ_true h, ih]
      unfold DAtom
      rw [IPos_append]
      have hI : IPos (P0 P) [n] = idxSet (e P) n := by
        rw [IPos_cons, IPos_nil, Set.inter_univ]
      rw [hI]
      show IPos (P0 P) (posnegList δ n).1 ∩ {m | ∀ j ∈ (posnegList δ n).2, m ∉ idxSet (e P) j}
          ∩ idxSet (e P) n = _
      ac_rfl
    · have hstep : genAtom (idxSet (e P)) Set.univ δ (n + 1) =
          genAtom (idxSet (e P)) Set.univ δ n ∩ (Set.univ \ idxSet (e P) n) := by
        show genAtom (idxSet (e P)) Set.univ δ n ∩
          (if δ n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [h]
      rw [hstep, posnegList_succ_false h, ih]
      unfold DAtom
      rw [negPart_append]
      have hZ : {m : ℕ | m ∉ idxSet (e P) n} = Set.univ \ idxSet (e P) n := by
        ext m; simp [Set.mem_sdiff]
      have hn : {m : ℕ | ∀ j ∈ [n], m ∉ idxSet (e P) j} = {m : ℕ | m ∉ idxSet (e P) n} := by
        ext m; simp
      rw [hn, hZ]
      show IPos (P0 P) (posnegList δ n).1 ∩ {m | ∀ j ∈ (posnegList δ n).2, m ∉ idxSet (e P) j}
          ∩ (Set.univ \ idxSet (e P) n) = _
      ac_rfl
end DomainTheory.NeighbourhoodSystems
