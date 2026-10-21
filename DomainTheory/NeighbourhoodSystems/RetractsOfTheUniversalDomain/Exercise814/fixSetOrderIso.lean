/-ai
The fixed-point set of a closure operator is order-isomorphic to the set of elements of the neighbourhood system reconstructed from that closure. The forward map sends a fixed point to the filter of principal up-sets of compact fixed points below it, the inverse is the directed supremum of the confirmed compact indices, each composite is the identity, and one fixed point lies below another exactly when its filter lies below the other filter.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsClosureOperator
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.domainOfClosure
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.toElementFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.toElementFilter_mono
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.le_of_toElementFilter_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.BasicInst34
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.fromElementFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.toElementFilter_fromElementFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.fromElementFilter_toElementFilter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : IsClosureOperator a)

/-- **Exercise 8.14, the domain isomorphism.** `Fix(a)` is order-isomorphic to
`|domainOfClosure h|`. -/
def fixSetOrderIso (h : IsClosureOperator a) : FixSet a ≃o (domainOfClosure h).Element where
  toFun := toElementFilter h
  invFun := fromElementFilter h
  left_inv := fromElementFilter_toElementFilter h
  right_inv := toElementFilter_fromElementFilter h
  map_rel_iff' := by
    intro y y'
    exact ⟨le_of_toElementFilter_le h, toElementFilter_mono h⟩

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
