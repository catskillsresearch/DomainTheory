/-ai
A compact fixed point lies in the principal up-set of another if and only if the underlying element of the first lies below the underlying element of the second.

Membership in the up-set is defined to be that inequality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.CompactFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)

@[simp] theorem mem_upFix {k q : CompactFix h} : q ∈ upFix h k ↔ k.1.1 ≤ q.1.1 := Iff.rfl

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
