module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.CompactFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)

/-- The principal up-set of a compact fixed point `k`: `{q ∣ k ⊑ q}`. This is the "neighbourhood"
of `k` in the reconstructed system (smaller compacts give *bigger* up-sets, matching the
information-order convention `Factoid 1.7a`). -/
def upFix (k : CompactFix h) : Set (CompactFix h) := {q | k.1.1 ≤ q.1.1}

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
