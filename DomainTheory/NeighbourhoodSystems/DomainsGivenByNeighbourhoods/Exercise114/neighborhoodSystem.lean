/-ai
The neighbourhood system of Exercise 1.14 has as neighbourhoods the whole set of natural numbers and the finite nonempty subsets, with the whole set as master neighbourhood. The master is nonempty and is a neighbourhood. In the intersection law, a neighbourhood contained in the intersection keeps the intersection nonempty. If the first set is the whole set, the intersection is the second neighbourhood. If the second set is the whole set, the intersection is the first, which is finite and nonempty. If both are finite, the intersection is finite and nonempty. Every neighbourhood is contained in the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.nonempty_of_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 1.14.** The neighbourhood system of finite non-empty subsets of `ℕ` (plus `Δ = ℕ`). -/
def neighborhoodSystem : NeighborhoodSystem ℕ where
  mem := mem
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    have hne : (X ∩ Y).Nonempty := (nonempty_of_mem hZ).mono hZsub
    rcases hX with hX | hX
    · rw [hX, Set.univ_inter]; exact hY
    · rcases hY with hY | hY
      · rw [hY, Set.inter_univ]; exact Or.inr hX
      · exact Or.inr ⟨hX.1.inter_of_left Y, hne⟩
  sub_master := fun _ => Set.subset_univ _

end DomainTheory.NeighbourhoodSystems.Exercise114
