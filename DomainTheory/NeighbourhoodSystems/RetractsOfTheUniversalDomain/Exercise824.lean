module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_8

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_3
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

section
/- concordance: source L5219 EXERCISE 8.24 coupled domain equations -/
-- Exercise824/PairSpace.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}

/-- Scott's pair space `(E → E) × (E → E)`: pairs of self-maps of `E`, as an actual
`NeighborhoodSystem` (Lecture III's product of two copies of the function space). -/
abbrev PairSpace : NeighborhoodSystem (ApproximableMap E E ⊕ ApproximableMap E E) :=
  prod (funSpace E E) (funSpace E E)

end Exercise824

end DomainTheory.NeighbourhoodSystems
end

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

section
namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}

/-- The `n`-th approximant's first component, as an actual approximable map `E → E`. -/
def aOp (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    ApproximableMap E E :=
  toApproxMap ((paired s t).iterElem n).fst

/-- Scott's `‖s‖ = fix(⟨s, t⟩)`'s first component, as an actual approximable map `E → E`. -/
def aStar (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) : ApproximableMap E E :=
  toApproxMap (paired s t).fixElement.fst

/-- The `n`-th approximant's second component, as an actual approximable map `E → E`. -/
def bOp (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    ApproximableMap E E :=
  toApproxMap ((paired s t).iterElem n).snd

/-- Scott's `‖t‖ = fix(⟨s, t⟩)`'s second component, as an actual approximable map `E → E`. -/
def bStar (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) : ApproximableMap E E :=
  toApproxMap (paired s t).fixElement.snd

/-- Scott's `s(a, b)`: the operator `(E → E) × (E → E) → (E → E)` induced by an approximable map
`s` out of the pair space, applied to two actual maps `a b : E → E`. -/
def binOp (f : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (a b : ApproximableMap E E) : ApproximableMap E E :=
  toApproxMap (f.toElementMap (pair (toFilter a) (toFilter b)))

theorem fst_mono {z z' : (PairSpace (E := E)).Element} (h : z ≤ z') : z.fst ≤ z'.fst := by
  intro X hX
  rw [mem_fst] at hX ⊢
  exact ⟨hX.1, h _ hX.2⟩

/-- The `n`-th approximant of `⟨s, t⟩` is exactly the pairing of `aOp`'s and `bOp`'s `n`-th
approximants (`Product.lean`'s `pair_fst_snd`, transported through the `toFilter`/`toApproxMap`
round trip). -/
theorem iterElem_pair_eq_pair (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    (paired s t).iterElem n = pair (toFilter (aOp s t n)) (toFilter (bOp s t n)) := by
  show (paired s t).iterElem n
      = pair (toFilter (toApproxMap ((paired s t).iterElem n).fst))
          (toFilter (toApproxMap ((paired s t).iterElem n).snd))
  rw [toFilter_toApproxMap, toFilter_toApproxMap, pair_fst_snd]

theorem iterElem_succ_pair (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    (paired s t).iterElem (n + 1) = (paired s t).toElementMap ((paired s t).iterElem n) := by
  show ((paired s t).comp ((paired s t).iterMap n)).toElementMap (PairSpace (E := E)).bot
      = (paired s t).toElementMap (((paired s t).iterMap n).toElementMap (PairSpace (E := E)).bot)
  rw [toElementMap_comp]

/-- **The mutual recursion on approximants**: `aOp s t (n+1) = binOp s (aOp s t n) (bOp s t n)`. -/
theorem aOp_succ (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    aOp s t (n + 1) = binOp s (aOp s t n) (bOp s t n) := by
  show toApproxMap ((paired s t).iterElem (n + 1)).fst
      = toApproxMap (s.toElementMap (pair (toFilter (aOp s t n)) (toFilter (bOp s t n))))
  rw [iterElem_succ_pair, toElementMap_paired, fst_pair, iterElem_pair_eq_pair]

/-- **The mutual recursion on approximants**: `bOp s t (n+1) = binOp t (aOp s t n) (bOp s t n)`. -/
theorem bOp_succ (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    bOp s t (n + 1) = binOp t (aOp s t n) (bOp s t n) := by
  show toApproxMap ((paired s t).iterElem (n + 1)).snd
      = toApproxMap (t.toElementMap (pair (toFilter (aOp s t n)) (toFilter (bOp s t n))))
  rw [iterElem_succ_pair, toElementMap_paired, snd_pair, iterElem_pair_eq_pair]

theorem iterElem_zero_pair (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    (paired s t).iterElem 0 = (PairSpace (E := E)).bot := by
  show (idMap (PairSpace (E := E))).toElementMap (PairSpace (E := E)).bot
      = (PairSpace (E := E)).bot
  rw [toElementMap_idMap]

theorem pair_bot_bot : pair ((funSpace E E).bot) ((funSpace E E).bot) = (PairSpace (E := E)).bot := by
  apply Element.ext
  intro W
  rw [mem_pair, mem_bot]
  constructor
  · rintro ⟨X, Y, hX, hY, rfl⟩
    rw [mem_bot] at hX hY
    rw [hX, hY, prod_master]
  · intro hW
    refine ⟨(funSpace E E).master, (funSpace E E).master, ?_, ?_, ?_⟩
    · rw [mem_bot]
    · rw [mem_bot]
    · rw [hW, prod_master]

theorem pairSpace_bot_fst : ((PairSpace (E := E)).bot).fst = (funSpace E E).bot := by
  rw [← pair_bot_bot, fst_pair]

theorem aOp_zero (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    aOp s t 0 = constMap E E.bot := by
  show toApproxMap ((paired s t).iterElem 0).fst = constMap E E.bot
  rw [iterElem_zero_pair, pairSpace_bot_fst, Exercise823.toApproxMap_bot_eq_constMap]

theorem pairSpace_bot_snd : ((PairSpace (E := E)).bot).snd = (funSpace E E).bot := by
  rw [← pair_bot_bot, snd_pair]

theorem bOp_zero (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    bOp s t 0 = constMap E E.bot := by
  show toApproxMap ((paired s t).iterElem 0).snd = constMap E E.bot
  rw [iterElem_zero_pair, pairSpace_bot_snd, Exercise823.toApproxMap_bot_eq_constMap]

/-- Every approximant pair `(aOp s t n, bOp s t n)` consists of finitary projections, provided
`s`/`t` send pairs of finitary projections to finitary projections. -/
theorem isFinitaryProjection_chain (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (hst : ∀ a b, FinitaryProjection a → FinitaryProjection b →
      FinitaryProjection (binOp s a b) ∧ FinitaryProjection (binOp t a b)) :
    ∀ n, FinitaryProjection (aOp s t n) ∧ FinitaryProjection (bOp s t n) := by
  intro n
  induction n with
  | zero =>
    rw [aOp_zero, bOp_zero]
    exact ⟨Exercise823.isFinitaryProjection_constMap_bot E,
      Exercise823.isFinitaryProjection_constMap_bot E⟩
  | succ k ih =>
    rw [aOp_succ, bOp_succ]
    exact hst _ _ ih.1 ih.2

theorem snd_mono {z z' : (PairSpace (E := E)).Element} (h : z ≤ z') : z.snd ≤ z'.snd := by
  intro X hX
  rw [mem_snd] at hX ⊢
  exact ⟨hX.1, h _ hX.2⟩

/-- **Exercise 8.24, Claim 1.** Provided `s`/`t` map pairs of finitary projections to finitary
projections, the simultaneous fixed point `(aStar s t, bStar s t)` really consists of finitary
projections. -/
theorem isFinitaryProjection_aStar_bStar (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (hst : ∀ a b, FinitaryProjection a → FinitaryProjection b →
      FinitaryProjection (binOp s a b) ∧ FinitaryProjection (binOp t a b)) :
    FinitaryProjection (aStar s t) ∧ FinitaryProjection (bStar s t) := by
  have hchain := isFinitaryProjection_chain s t hst
  have hsubA : ∀ n, subFilter (((paired s t).iterElem n).fst) = ((paired s t).iterElem n).fst := by
    intro n
    apply toApproxMap_injective
    rw [toApproxMap_subFilter]
    show sub (aOp s t n) = aOp s t n
    exact sub_eq_self_of_isFinitaryProjection (hchain n).1
  have hsubB : ∀ n, subFilter (((paired s t).iterElem n).snd) = ((paired s t).iterElem n).snd := by
    intro n
    apply toApproxMap_injective
    rw [toApproxMap_subFilter]
    show sub (bOp s t n) = bOp s t n
    exact sub_eq_self_of_isFinitaryProjection (hchain n).2
  have hdirA : ∀ i j : ℕ, ∃ k, ((paired s t).iterElem i).fst ≤ ((paired s t).iterElem k).fst ∧
      ((paired s t).iterElem j).fst ≤ ((paired s t).iterElem k).fst :=
    fun i j => ⟨max i j, fst_mono (iterElem_mono (paired s t) (le_max_left i j)),
      fst_mono (iterElem_mono (paired s t) (le_max_right i j))⟩
  have hdirB : ∀ i j : ℕ, ∃ k, ((paired s t).iterElem i).snd ≤ ((paired s t).iterElem k).snd ∧
      ((paired s t).iterElem j).snd ≤ ((paired s t).iterElem k).snd :=
    fun i j => ⟨max i j, snd_mono (iterElem_mono (paired s t) (le_max_left i j)),
      snd_mono (iterElem_mono (paired s t) (le_max_right i j))⟩
  have hdirSubA : ∀ i j : ℕ, ∃ k, subFilter (((paired s t).iterElem i).fst) ≤
      subFilter (((paired s t).iterElem k).fst) ∧
      subFilter (((paired s t).iterElem j).fst) ≤ subFilter (((paired s t).iterElem k).fst) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdirA i j
    exact ⟨k, by rw [hsubA i, hsubA k]; exact hik, by rw [hsubA j, hsubA k]; exact hjk⟩
  have hdirSubB : ∀ i j : ℕ, ∃ k, subFilter (((paired s t).iterElem i).snd) ≤
      subFilter (((paired s t).iterElem k).snd) ∧
      subFilter (((paired s t).iterElem j).snd) ≤ subFilter (((paired s t).iterElem k).snd) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdirB i j
    exact ⟨k, by rw [hsubB i, hsubB k]; exact hik, by rw [hsubB j, hsubB k]; exact hjk⟩
  have hEqA : (paired s t).fixElement.fst =
      iSupDirected (fun n => ((paired s t).iterElem n).fst) hdirA := by
    apply Element.ext
    intro X
    rw [mem_fst, mem_fixElement, mem_iSupDirected]
    constructor
    · rintro ⟨hX, n, hn⟩
      exact ⟨n, mem_fst.mpr ⟨hX, (mem_iterElem (paired s t) n).mpr hn⟩⟩
    · rintro ⟨n, hn⟩
      rw [mem_fst] at hn
      exact ⟨hn.1, n, (mem_iterElem (paired s t) n).mp hn.2⟩
  have hEqB : (paired s t).fixElement.snd =
      iSupDirected (fun n => ((paired s t).iterElem n).snd) hdirB := by
    apply Element.ext
    intro X
    rw [mem_snd, mem_fixElement, mem_iSupDirected]
    constructor
    · rintro ⟨hX, n, hn⟩
      exact ⟨n, mem_snd.mpr ⟨hX, (mem_iterElem (paired s t) n).mpr hn⟩⟩
    · rintro ⟨n, hn⟩
      rw [mem_snd] at hn
      exact ⟨hn.1, n, (mem_iterElem (paired s t) n).mp hn.2⟩
  have hkeyA : subFilter ((paired s t).fixElement.fst) = (paired s t).fixElement.fst := by
    rw [hEqA, subFilter_iSupDirected _ hdirA hdirSubA]
    apply Element.ext
    intro Z
    rw [mem_iSupDirected, mem_iSupDirected]
    simp_rw [hsubA]
  have hkeyB : subFilter ((paired s t).fixElement.snd) = (paired s t).fixElement.snd := by
    rw [hEqB, subFilter_iSupDirected _ hdirB hdirSubB]
    apply Element.ext
    intro Z
    rw [mem_iSupDirected, mem_iSupDirected]
    simp_rw [hsubB]
  refine ⟨?_, ?_⟩
  · show FinitaryProjection (toApproxMap (paired s t).fixElement.fst)
    apply isFinitaryProjection_of_sub_eq_self
    rw [← toApproxMap_subFilter, hkeyA]
  · show FinitaryProjection (toApproxMap (paired s t).fixElement.snd)
    apply isFinitaryProjection_of_sub_eq_self
    rw [← toApproxMap_subFilter, hkeyB]

/-- **Exercise 8.24, Claim 2 (initiality with respect to projections).** If `a, b` is *any* other
pair of finitary projections that is a pre-fixed point of the same pair of operators
(`binOp s a b ≤ a`, `binOp t a b ≤ b`, in particular any exact alternative solution), then
`(aStar s t, bStar s t)`'s domains embed as literal subsystems of `a`'s and `b`'s domains:
`D_{aStar s t} ◁ D_a`, `D_{bStar s t} ◁ D_b` — Scott's "the initial solution... with respect to
projections", for both components simultaneously. -/
theorem fixedNbhd_aStar_bStar_subsystem (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (hst : ∀ a b, FinitaryProjection a → FinitaryProjection b →
      FinitaryProjection (binOp s a b) ∧ FinitaryProjection (binOp t a b))
    {a b : ApproximableMap E E} (ha : FinitaryProjection a) (hb : FinitaryProjection b)
    (hpreA : binOp s a b ≤ a) (hpreB : binOp t a b ≤ b) :
    fixedNbhd (aStar s t) ◁ fixedNbhd a ∧ fixedNbhd (bStar s t) ◁ fixedNbhd b := by
  have h1 : s.toElementMap (pair (toFilter a) (toFilter b)) ≤ toFilter a := by
    have hpreA' : toApproxMap (s.toElementMap (pair (toFilter a) (toFilter b))) ≤
        toApproxMap (toFilter a) := by
      show binOp s a b ≤ toApproxMap (toFilter a)
      rw [toApproxMap_toFilter]
      exact hpreA
    have hiff := (funSpaceEquiv E E).le_iff_le
      (x := s.toElementMap (pair (toFilter a) (toFilter b))) (y := toFilter a)
    rw [funSpaceEquiv_apply, funSpaceEquiv_apply] at hiff
    exact hiff.mp hpreA'
  have h2 : t.toElementMap (pair (toFilter a) (toFilter b)) ≤ toFilter b := by
    have hpreB' : toApproxMap (t.toElementMap (pair (toFilter a) (toFilter b))) ≤
        toApproxMap (toFilter b) := by
      show binOp t a b ≤ toApproxMap (toFilter b)
      rw [toApproxMap_toFilter]
      exact hpreB
    have hiff := (funSpaceEquiv E E).le_iff_le
      (x := t.toElementMap (pair (toFilter a) (toFilter b))) (y := toFilter b)
    rw [funSpaceEquiv_apply, funSpaceEquiv_apply] at hiff
    exact hiff.mp hpreB'
  have hle : (paired s t).toElementMap (pair (toFilter a) (toFilter b)) ≤
      pair (toFilter a) (toFilter b) := by
    rw [toElementMap_paired]
    exact pair_le_pair_iff.mpr ⟨h1, h2⟩
  have hfix : (paired s t).fixElement ≤ pair (toFilter a) (toFilter b) :=
    fixElement_le_of_toElementMap_le (paired s t) hle
  have hfstle : (paired s t).fixElement.fst ≤ toFilter a := by
    have := fst_mono hfix; rwa [fst_pair] at this
  have hsndle : (paired s t).fixElement.snd ≤ toFilter b := by
    have := snd_mono hfix; rwa [snd_pair] at this
  have hAle : aStar s t ≤ a := by
    show toApproxMap (paired s t).fixElement.fst ≤ a
    rw [← toApproxMap_toFilter a]
    exact toApproxMap_monotone hfstle
  have hBle : bStar s t ≤ b := by
    show toApproxMap (paired s t).fixElement.snd ≤ b
    rw [← toApproxMap_toFilter b]
    exact toApproxMap_monotone hsndle
  obtain ⟨hFinA, hFinB⟩ := isFinitaryProjection_aStar_bStar s t hst
  exact ⟨(isFinitaryProjection_le_iff_fixedNbhd_subsystem hFinA ha).mp hAle,
    (isFinitaryProjection_le_iff_fixedNbhd_subsystem hFinB hb).mp hBle⟩

theorem toElementMap_fixElement_fst (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    s.toElementMap (paired s t).fixElement = (paired s t).fixElement.fst := by
  have h : (paired s t).toElementMap (paired s t).fixElement = (paired s t).fixElement :=
    toElementMap_fixElement (paired s t)
  rw [toElementMap_paired] at h
  have h' := congrArg NeighborhoodSystem.Element.fst h
  rwa [fst_pair] at h'

/-- `(aStar s t, bStar s t)` is a *genuine* fixed point of the pair `(s, t)`. -/
theorem binOp_aStar_bStar_left (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    binOp s (aStar s t) (bStar s t) = aStar s t := by
  unfold binOp aStar bStar
  rw [toFilter_toApproxMap, toFilter_toApproxMap, pair_fst_snd, toElementMap_fixElement_fst]

theorem toElementMap_fixElement_snd (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    t.toElementMap (paired s t).fixElement = (paired s t).fixElement.snd := by
  have h : (paired s t).toElementMap (paired s t).fixElement = (paired s t).fixElement :=
    toElementMap_fixElement (paired s t)
  rw [toElementMap_paired] at h
  have h' := congrArg NeighborhoodSystem.Element.snd h
  rwa [snd_pair] at h'

/-- `(aStar s t, bStar s t)` is a *genuine* fixed point of the pair `(s, t)`. -/
theorem binOp_aStar_bStar_right (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    binOp t (aStar s t) (bStar s t) = bStar s t := by
  unfold binOp aStar bStar
  rw [toFilter_toApproxMap, toFilter_toApproxMap, pair_fst_snd, toElementMap_fixElement_snd]

/-- **Exercise 8.24, Claim 2 (the domain equations).** Given any correspondences `S, T` (bundling,
for each pair of maps, a type and a domain over it) with `Fix(binOp s a b) ≅ S(a,b)` and
`Fix(binOp t a b) ≅ T(a,b)` for every pair of finitary projections `a, b` (Scott's hypotheses
`D_{s(a,b)} ≅ S(D_a,D_b)`, `D_{t(a,b)} ≅ T(D_a,D_b)`), substituting the *exact* simultaneous fixed
point `a := aStar s t`, `b := bStar s t` and using `binOp_aStar_bStar_left/right` gives
`Fix(aStar s t) ≅ S(aStar s t, bStar s t)` and `Fix(bStar s t) ≅ T(aStar s t, bStar s t)`
unconditionally — Scott's `D ≅ S(D,E)`, `E ≅ T(D,E)`. -/
theorem fixedDomain_aStar_bStar_iso (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (hst : ∀ a b, FinitaryProjection a → FinitaryProjection b →
      FinitaryProjection (binOp s a b) ∧ FinitaryProjection (binOp t a b))
    (S T : ApproximableMap E E → ApproximableMap E E → Σ β : Type, NeighborhoodSystem β)
    (hS : ∀ a b, FinitaryProjection a → FinitaryProjection b →
      Nonempty (Fix (binOp s a b) ≃o (S a b).2.Element))
    (hT : ∀ a b, FinitaryProjection a → FinitaryProjection b →
      Nonempty (Fix (binOp t a b) ≃o (T a b).2.Element)) :
    Nonempty (Fix (aStar s t) ≃o (S (aStar s t) (bStar s t)).2.Element) ∧
      Nonempty (Fix (bStar s t) ≃o (T (aStar s t) (bStar s t)).2.Element) := by
  obtain ⟨hFinA, hFinB⟩ := isFinitaryProjection_aStar_bStar s t hst
  have h1 := hS (aStar s t) (bStar s t) hFinA hFinB
  have h2 := hT (aStar s t) (bStar s t) hFinA hFinB
  rw [binOp_aStar_bStar_left] at h1
  rw [binOp_aStar_bStar_right] at h2
  exact ⟨h1, h2⟩

end Exercise824
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise824
set_option linter.unusedVariables false

theorem example_824 : And
  (And
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (s t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              And
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
        ∀
          (S T :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E →
              @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E →
                @Sigma Type fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
          (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
                  Nonempty
                    (@OrderIso
                      (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S a b))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S a b)))
                      (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                        fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b) y)
                          y)
                      (@Preorder.toLE
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S a b))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S a b)))
                        (@PartialOrder.toPreorder
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b)))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))))))) →
            (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
                    Nonempty
                      (@OrderIso
                        (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a b))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a b)))
                        (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                          fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b) y)
                            y)
                        (@Preorder.toLE
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (T a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (T a b)))
                          (@PartialOrder.toPreorder
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                              (@Sigma.fst Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b))
                              (@Sigma.snd Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b)))
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                              (@Sigma.fst Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b))
                              (@Sigma.snd Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                                (T a b))))))) →
              And
                (Nonempty
                  (@OrderIso
                    (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                      (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                    (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                      fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t) y)
                        y)
                    (@Preorder.toLE
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                      (@PartialOrder.toPreorder
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))))))
                (Nonempty
                  (@OrderIso
                    (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                      (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                    (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                      fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t) y)
                        y)
                    (@Preorder.toLE
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                      (@PartialOrder.toPreorder
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))))))))
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (s t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              And
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
        ∀ {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                      (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b) a →
                @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                      (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                        (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                    (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b) b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.Subsystem α
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem α
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E b))))
  (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (s t :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap
        (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
    (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
            And
              (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
              (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
      And
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
          (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))) :=
  @And.intro
  (And
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (s t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              And
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
        ∀
          (S T :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E →
              @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E →
                @Sigma Type fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
          (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
                  Nonempty
                    (@OrderIso
                      (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S a b))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S a b)))
                      (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                        fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b) y)
                          y)
                      (@Preorder.toLE
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S a b))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S a b)))
                        (@PartialOrder.toPreorder
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b)))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))))))) →
            (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
                    Nonempty
                      (@OrderIso
                        (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a b))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a b)))
                        (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                          fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b) y)
                            y)
                        (@Preorder.toLE
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (T a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (T a b)))
                          (@PartialOrder.toPreorder
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                              (@Sigma.fst Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b))
                              (@Sigma.snd Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b)))
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                              (@Sigma.fst Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b))
                              (@Sigma.snd Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                                (T a b))))))) →
              And
                (Nonempty
                  (@OrderIso
                    (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                      (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                    (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                      fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t) y)
                        y)
                    (@Preorder.toLE
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                      (@PartialOrder.toPreorder
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))))))
                (Nonempty
                  (@OrderIso
                    (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                      (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                    (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                      fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t) y)
                        y)
                    (@Preorder.toLE
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                      (@PartialOrder.toPreorder
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))))))))
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (s t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              And
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
        ∀ {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                      (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b) a →
                @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                      (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                        (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                    (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b) b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.Subsystem α
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem α
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E b))))
  (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (s t :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap
        (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
    (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
            And
              (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
              (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
      And
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
          (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
  (@And.intro
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (s t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              And
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
        ∀
          (S T :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E →
              @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E →
                @Sigma Type fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
          (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
                  Nonempty
                    (@OrderIso
                      (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S a b))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S a b)))
                      (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                        fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b) y)
                          y)
                      (@Preorder.toLE
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S a b))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S a b)))
                        (@PartialOrder.toPreorder
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b)))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))))))) →
            (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
                    Nonempty
                      (@OrderIso
                        (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a b))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a b)))
                        (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                          fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b) y)
                            y)
                        (@Preorder.toLE
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (T a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (T a b)))
                          (@PartialOrder.toPreorder
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                              (@Sigma.fst Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b))
                              (@Sigma.snd Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b)))
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                              (@Sigma.fst Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b))
                              (@Sigma.snd Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                                (T a b))))))) →
              And
                (Nonempty
                  (@OrderIso
                    (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                      (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                    (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                      fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t) y)
                        y)
                    (@Preorder.toLE
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                      (@PartialOrder.toPreorder
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))))))
                (Nonempty
                  (@OrderIso
                    (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                      (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                    (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                      fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t) y)
                        y)
                    (@Preorder.toLE
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                      (@PartialOrder.toPreorder
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))))))))
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (s t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              And
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
        ∀ {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                      (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b) a →
                @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                      (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                        (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                    (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b) b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.Subsystem α
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem α
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E b)))
    @DomainTheory.NeighbourhoodSystems.Exercise824.fixedDomain_aStar_bStar_iso
    @DomainTheory.NeighbourhoodSystems.Exercise824.fixedNbhd_aStar_bStar_subsystem)
  @DomainTheory.NeighbourhoodSystems.Exercise824.isFinitaryProjection_aStar_bStar

end DomainTheory.NeighbourhoodSystems.Exercise824
namespace DomainTheory.NeighbourhoodSystems.Example15

end DomainTheory.NeighbourhoodSystems.Example15
namespace DomainTheory.NeighbourhoodSystems.Exercise722
/-- Countability of the neighbourhoods of `S`, via the `SExpr` presentation.
Picking a preimage uses Mathlib's `Surjective.countable` (hence `Classical.choice`);
the syntax `SExpr` itself is countable choice-free. -/
instance Ssys_countable : Countable {S : Set (List Bool) // Ssys.mem S} := by
  classical
  let f (e : SExpr) : {S : Set (List Bool) // InS S} :=
    if h : (denote e).Nonempty then ⟨denote e, InS_denote_of_nonempty h⟩
    else ⟨Set.univ, InS.univ⟩
  have : Countable {S : Set (List Bool) // InS S} :=
    Function.Surjective.countable (f := f) fun ⟨X, hX⟩ => by
      obtain ⟨e, he⟩ := InS_exists_denote hX
      refine ⟨e, ?_⟩
      have hne : (denote e).Nonempty := he.symm ▸ hX.nonempty
      dsimp [f]
      rw [dite_eq_left hne]
      exact Subtype.ext he
  exact Countable.of_equiv ({S : Set (List Bool) // InS S})
    (Equiv.subtypeEquivRight fun _ => Ssys_mem.symm)

end DomainTheory.NeighbourhoodSystems.Exercise722
namespace DomainTheory.NeighbourhoodSystems.Example15
/-- **New corollary for Example 1.5.** The finite powerset system is countable, so the first
sentence of Theorem 8.8 applies. Scott does not separately state this embedding. -/
theorem P4_embeds : neighborhoodSystem ⊴ U :=
  theorem_8_8 neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example15
namespace DomainTheory.NeighbourhoodSystems.Exercise722
/-- **New corollary for Exercise 7.22.** Countability is `Ssys_countable` (via `SExpr`), so the
first sentence of Theorem 8.8 applies. Scott does not separately state this embedding. -/
theorem Ssys_embeds : Ssys ⊴ U :=
  theorem_8_8 Ssys

end DomainTheory.NeighbourhoodSystems.Exercise722
