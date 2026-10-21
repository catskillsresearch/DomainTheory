/-ai
The elements fixed by the packaged map subApprox are order-isomorphic to the approximable endomaps fixed by sub. The forward map extracts the approximable map of a fixed element, and the backward map sends a fixed endomap to its filter. A fixed element has filter transport equal to itself, so extracting maps shows that sub of the extracted map equals the extracted map. The filter of a fixed endomap is fixed because the filter transport of that filter is the filter of sub of the map. The two round trips are the round trips of the function-space equivalence, and the order is the order of that equivalence.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toFilter_toApproxMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toApproxMap_toFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toApproxMap_subFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subApprox
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toElementMap_subApprox

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

/-- **`Fix(subApprox) ≃o {f ∣ sub f = f}`.** `subApprox.toElementMap φ = φ` unfolds (via
`toElementMap_subApprox`/`subFilter`) to `toFilter (sub (toApproxMap φ)) = φ`, i.e. exactly
`sub (toApproxMap φ) = toApproxMap φ` after transporting through `toApproxMap`/`toFilter`'s round
trips. -/
def subApproxFixIso :
    {φ : (funSpace E E).Element // subApprox.toElementMap φ = φ} ≃o
      {f : ApproximableMap E E // sub f = f} where
  toFun φ := ⟨toApproxMap φ.1, by
    have h1 : subFilter φ.1 = φ.1 := (toElementMap_subApprox φ.1).symm.trans φ.2
    have h2 : toApproxMap (subFilter φ.1) = toApproxMap φ.1 := congrArg toApproxMap h1
    rwa [toApproxMap_subFilter] at h2⟩
  invFun f := ⟨toFilter f.1, by
    rw [toElementMap_subApprox]
    show subFilter (toFilter f.1) = toFilter f.1
    unfold subFilter
    rw [toApproxMap_toFilter, f.2]⟩
  left_inv φ := Subtype.ext (toFilter_toApproxMap φ.1)
  right_inv f := Subtype.ext (toApproxMap_toFilter f.1)
  map_rel_iff' := by
    intro φ ψ
    show toApproxMap φ.1 ≤ toApproxMap ψ.1 ↔ φ.1 ≤ ψ.1
    exact (funSpaceEquiv E E).map_rel_iff

end Sub8_6

end DomainTheory.NeighbourhoodSystems
