/-ai
If Y is a neighbourhood of the function space and the closed form of the product of d at the approximable map of x lies in Y, then some neighbourhood X lies in x, is contained in Y, and is self-related by the product.

A function-space neighbourhood is the step function of a list, and the existence theorem for step functions supplies X.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.exists_X_of_mem_stepFun

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap


/-- **Exercise 8.27(b)(3), the `⟹` half, closed for any `d` at all.** Destructure the general
`Y : Set (ApproximableMap U U)` via `funSpace_mem_iff` into `Y = stepFun L`, then apply
`exists_X_of_mem_stepFun`. -/
theorem hii_hard_direction (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y : Set (ApproximableMap U U)} (hYE : (funSpace U U).mem Y)
    (hmem : piDApply d (toApproxMap x) ∈ Y) :
    ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X := by
  obtain ⟨⟨L, _, rfl⟩, _⟩ := hYE
  exact exists_X_of_mem_stepFun d x L hmem

end DomainTheory.NeighbourhoodSystems
