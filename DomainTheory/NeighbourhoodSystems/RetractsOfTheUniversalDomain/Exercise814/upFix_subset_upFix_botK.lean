/-ai
The principal up-set of any compact fixed point is contained in the principal up-set of the bottom compact.

Every fixed point lies above the bottom fixed point.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.botFix_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.CompactFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.botK
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)

theorem upFix_subset_upFix_botK (k : CompactFix h) : upFix h k ⊆ upFix h (botK h) :=
  fun q _ => botFix_le h q.1

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
