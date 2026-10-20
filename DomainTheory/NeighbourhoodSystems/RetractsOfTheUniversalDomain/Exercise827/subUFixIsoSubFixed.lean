module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subUFixIso

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **`subU`'s fixed points are exactly the finitary projections of `𝒰`** (Exercise 8.27's
opening sentence, precisely): composing `subUFixIso` with Theorem 8.6(b)(ii)'s `subApproxFixIso`
identifies `Fix(subU)` with `{f : 𝒰→𝒰 ∣ sub f = f}`, which by Theorem 8.6(a)'s
`sub_eq_self_iff_isFinitaryProjection` is exactly `{f ∣ IsFinitaryProjection f}`. -/
noncomputable def subUFixIsoSubFixed :
    {w : U.Element // subU.toElementMap w = w} ≃o
      {f : ApproximableMap U U // sub f = f} :=
  subUFixIso.trans Sub8_6.subApproxFixIso

end DomainTheory.NeighbourhoodSystems
