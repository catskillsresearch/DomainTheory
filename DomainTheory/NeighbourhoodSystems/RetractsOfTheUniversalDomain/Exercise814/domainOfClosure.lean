/-ai
The neighbourhood system associated with a closure operator has the compact fixed points as tokens and takes as neighbourhoods the principal up-sets of those compacts, with master the up-set of the bottom compact. The master contains the bottom compact, so it is nonempty, and it is a neighbourhood by construction. Every neighbourhood is contained in the master because every up-set is contained in the up-set of the bottom compact. Given two neighbourhoods and a third neighbourhood contained in their intersection, the token of the third lies in both up-sets, and the up-set of the join of the first two compacts above that token equals the intersection, so the intersection law holds.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.CompactFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.botK
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.joinCompactFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.self_mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.upFix_subset_upFix_botK
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.upFix_inter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)

/-- **The reconstructed neighbourhood system.** Tokens are the compact fixed points of `a`;
neighbourhoods are their principal up-sets. -/
def domainOfClosure (h : ClosureOperator a) : NeighborhoodSystem (CompactFix h) where
  mem S := ∃ k : CompactFix h, S = upFix h k
  master := upFix h (botK h)
  master_nonempty := ⟨botK h, self_mem_upFix h (botK h)⟩
  master_mem := ⟨botK h, rfl⟩
  sub_master := by rintro S ⟨k, rfl⟩; exact upFix_subset_upFix_botK h k
  inter_mem := by
    rintro S1 S2 Z ⟨k1, rfl⟩ ⟨k2, rfl⟩ ⟨k3, rfl⟩ hZsub
    obtain ⟨hk13, hk23⟩ := hZsub (self_mem_upFix h k3)
    exact ⟨joinCompactFix h hk13 hk23, upFix_inter h k1 k2 hk13 hk23⟩

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
