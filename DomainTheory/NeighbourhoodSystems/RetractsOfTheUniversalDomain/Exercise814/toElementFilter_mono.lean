/-ai
The forward map from fixed points to elements of the reconstructed domain is monotone.

A compact that lies below the smaller fixed point still lies below the larger one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.toElementFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : IsClosureOperator a)

theorem toElementFilter_mono {y y' : FixSet a} (hyy' : y.1 ≤ y'.1) :
    toElementFilter h y ≤ toElementFilter h y' :=
  fun _ ⟨k, hSeq, hky⟩ => ⟨k, hSeq, hky.trans hyy'⟩

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
