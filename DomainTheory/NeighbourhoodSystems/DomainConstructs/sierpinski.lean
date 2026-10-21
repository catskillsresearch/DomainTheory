/-ai
The Sierpiński domain is the neighbourhood system on a one-point token type whose neighbourhoods are the full token set and the empty set, with the full set as master. The unique token lies in the master, the master is a neighbourhood, the intersection of any two of these neighbourhoods is again one of them, and every neighbourhood is contained in the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

/-- The **Sierpiński domain** `𝒪`: the system over a one-token type whose neighbourhoods are `Δ`
(`univ`) and `∅`. Its elements are `⊥` (only `Δ`) and `⊤` (also `∅`), i.e. the two-point domain. -/
def sierpinski : NeighborhoodSystem Unit where
  mem N := N = Set.univ ∨ N = ∅
  master := Set.univ
  master_nonempty := ⟨(), Set.mem_univ _⟩
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y Z hX hY hZ _
    rcases hX with rfl | rfl
    · rcases hY with rfl | rfl
      · left; rw [Set.univ_inter]
      · right; rw [Set.univ_inter]
    · right; rw [Set.empty_inter]
  sub_master := fun _ => Set.subset_univ _

end DomainTheory.NeighbourhoodSystems.Exercise325
