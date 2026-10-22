/-ai
If two operators on pairs of self-maps send finitary projections to finitary projections, and two finitary projections each lie above the corresponding operator applied to the pair, then the fixed neighbourhood system of the first simultaneous component is a literal subsystem of the first projection's fixed neighbourhood system, and likewise for the second component.

Transport each inequality across the order equivalence of the function space, so that each operator applied to the pair of filters lies below the corresponding filter. Pairing those inequalities shows that the paired operator applied to the pair of filters lies below that pair. Minimality of the fixed element puts the fixed element below the pair. Monotonicity of the two projections puts the two components of the fixed element below the two filters. Reading maps back puts the simultaneous components below the two projections. The order criterion for finitary projections converts those inequalities into the two subsystem relations.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.fst_mono
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.snd_mono
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.isFinitaryProjection_aStar_bStar

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}


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

end Exercise824
end DomainTheory.NeighbourhoodSystems
