/-ai
If two compact fixed points have the same principal up-set, their underlying elements are equal.

Each compact belongs to its own up-set, hence to the other up-set, and the two inequalities give equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.CompactFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.self_mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)

/-- The generator of a non-empty up-set is unique. -/
theorem upFix_injOn {k k' : CompactFix h} (heq : upFix h k = upFix h k') : k.1.1 = k'.1.1 :=
  le_antisymm ((Set.ext_iff.mp heq k').mpr (self_mem_upFix h k'))
    ((Set.ext_iff.mp heq k).mp (self_mem_upFix h k))

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
