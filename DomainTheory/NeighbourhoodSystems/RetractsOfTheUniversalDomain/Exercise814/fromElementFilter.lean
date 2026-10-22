module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.domainOfClosure
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.confirmedIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.BasicInst34
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.confirmedIdx_directed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)

/-- **The backward map `|domainOfClosure h| → Fix(a)`**: the directed union of all confirmed
compacts. -/
def fromElementFilter (g : (domainOfClosure h).Element) : FixSet a :=
  ⟨iSupDirected (fun i : confirmedIdx h g => i.1.1.1) (confirmedIdx_directed h g),
    toElementMap_iSupDirected_fixed _ (confirmedIdx_directed h g) (fun i => i.1.1.2)⟩

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
