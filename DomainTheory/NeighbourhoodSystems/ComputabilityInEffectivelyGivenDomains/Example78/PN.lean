/-ai
The powerset domain is the neighbourhood system on the natural numbers whose neighbourhoods are the cofinite sets of unset bit positions, with master the set of all natural numbers. The master is the neighbourhood of index zero. The intersection of two neighbourhoods is the neighbourhood of the bitwise disjunction of their indices. Every neighbourhood is contained in the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd_inter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example78

open Domain.Recursive NeighborhoodSystem

/-- **The powerset domain `PN`** as a neighbourhood system over the token type `ℕ`: the
neighbourhoods are the cofinite sets `nbhd n`, with master `Δ = ℕ`. Closure under intersection is
`nbhd_inter` (the intersection is `nbhd (n ||| m)`), so no consistency hypothesis is even needed. -/
def PN : NeighborhoodSystem ℕ where
  mem Y := ∃ n, Y = nbhd n
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := ⟨0, nbhd_zero.symm⟩
  inter_mem := by
    rintro X Y Z ⟨a, rfl⟩ ⟨b, rfl⟩ _ _
    exact ⟨myLor a b, nbhd_inter a b⟩
  sub_master := by rintro X _; exact Set.subset_univ X

end DomainTheory.NeighbourhoodSystems.Example78
