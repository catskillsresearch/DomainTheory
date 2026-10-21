/-ai
If an operator on self-maps sends finitary projections to finitary projections, and a finitary projection lies above its image under the operator, then the fixed neighbourhood system of the operator's fixed point is a literal subsystem of the fixed neighbourhood system of that projection.

Rewrite the inequality so that the right-hand side is the map read from the filter of the projection, and transport it across the order equivalence of the function space to an inequality of elements. Minimality of the fixed element puts that element below the filter. Monotonicity of reading maps, after rewriting the projection as the map of its own filter, puts the fixed point below the projection. The order criterion for finitary projections converts that inequality into the subsystem relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise816
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.isFinitaryProjection_fixOp

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}


/-- **Exercise 8.23, Claim 2 (initiality with respect to projections).** If `a` is *any* other
finitary projection that is a pre-fixed point of the same operator (`tOp t a ≤ a`, in particular
any exact alternative solution `tOp t a = a`), then `‖t‖`'s domain embeds as a literal subsystem of
`a`'s domain: `D_{‖t‖} ◁ D_a` (hence certainly `D_{‖t‖} ⊴ D_a`, Lemma 6.15) — Scott's "the initial
solution... with respect to projections". The proof is Theorem 4.1's minimality
(`fixElement_le_of_toElementMap_le`) transported through Exercise 8.16's order-isomorphism
`a ≤ b ↔ D_a ◁ D_b`. -/
theorem fixedNbhd_fixOp_subsystem (t : ApproximableMap (funSpace E E) (funSpace E E))
    (ht : ∀ a, IsFinitaryProjection a → IsFinitaryProjection (tOp t a))
    {a : ApproximableMap E E} (ha : IsFinitaryProjection a) (hpre : tOp t a ≤ a) :
    fixedNbhd (fixOp t) ◁ fixedNbhd a := by
  have hpre' : toApproxMap (t.toElementMap (toFilter a)) ≤ toApproxMap (toFilter a) := by
    show tOp t a ≤ toApproxMap (toFilter a)
    rw [toApproxMap_toFilter]
    exact hpre
  have h1 : t.toElementMap (toFilter a) ≤ toFilter a := by
    have hiff := (funSpaceEquiv E E).le_iff_le
      (x := t.toElementMap (toFilter a)) (y := toFilter a)
    rw [funSpaceEquiv_apply, funSpaceEquiv_apply] at hiff
    exact hiff.mp hpre'
  have h2 : t.fixElement ≤ toFilter a := fixElement_le_of_toElementMap_le t h1
  have hle : fixOp t ≤ a := by
    show toApproxMap t.fixElement ≤ a
    rw [← toApproxMap_toFilter a]
    exact toApproxMap_monotone h2
  exact (isFinitaryProjection_le_iff_fixedNbhd_subsystem
    (isFinitaryProjection_fixOp t ht) ha).mp hle

end Exercise823
end DomainTheory.NeighbourhoodSystems
