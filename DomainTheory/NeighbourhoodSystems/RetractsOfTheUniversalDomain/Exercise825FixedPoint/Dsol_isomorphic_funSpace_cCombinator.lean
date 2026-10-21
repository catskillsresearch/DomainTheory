/-ai
The fixed neighbourhood of the fixed point of the continuous operator of the combinator is isomorphic to the function space from that neighbourhood into the fixed neighbourhood of the combinator.

The operator sends finitary projections to finitary projections, so its fixed point is a finitary projection. The fixed neighbourhood is then order-isomorphic to the fixed set of that projection. The fixed-point correspondence of Exercise 8.23, instantiated at the arrow domain, identifies that fixed set with the function space into the fixed neighbourhood of the combinator. Compose the two order isomorphisms.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Closing
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.isFinitaryProjection_cCombinator
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.ht_tOpMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.hT_TArrow

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap



















/-- **`D ≅ D → 𝒰^∞` for `D := fixedNbhd (fixOp t)`.** Exercise 8.23's `fixedDomain_fixOp_iso_T`
gives `Fix(‖t‖) ≅ D → D_c`; `fixedNbhd_elementIso_fix` identifies `D`'s own element type with
`Fix(‖t‖)`, and `fixedNbhd_cCombinator_isomorphic` identifies `D_c` with `𝒰^∞`. -/
theorem Dsol_isomorphic_funSpace_cCombinator :
    fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) ≅ᴰ
      funSpace (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator))) (fixedNbhd cCombinator) := by
  have hht := ht_tOpMap cCombinator isFinitaryProjection_cCombinator
  have hFP := Exercise823.isFinitaryProjection_fixOp (tOpMap cCombinator) hht
  have h1 : Nonempty ((fixedNbhd (Exercise823.fixOp (tOpMap cCombinator))).Element ≃o
      Exercise823.Fix (Exercise823.fixOp (tOpMap cCombinator))) :=
    ⟨fixedNbhd_elementIso_fix hFP⟩
  have h2 := Exercise823.fixedDomain_fixOp_iso_T (tOpMap cCombinator) hht TArrow hT_TArrow
  exact h1.elim fun e1 => h2.elim fun e2 => ⟨e1.trans e2⟩

end DomainTheory.NeighbourhoodSystems
