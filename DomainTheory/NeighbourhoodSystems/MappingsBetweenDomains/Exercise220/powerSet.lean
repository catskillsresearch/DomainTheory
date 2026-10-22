/-ai
The powerset neighbourhood system has the natural numbers as tokens and the cofinite sets as neighbourhoods. The master neighbourhood is the universe, which is nonempty, and its complement is empty. The intersection of cofinite sets is cofinite because the complement of an intersection is the union of the complements. Every neighbourhood is contained in the universe.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 2.20 — the powerset system `𝒫`.** Tokens `ℕ`; the neighbourhoods are the cofinite
sets, closed under finite intersection (`(X ∩ Y)ᶜ = Xᶜ ∪ Yᶜ`). -/
def powerSet : NeighborhoodSystem ℕ where
  mem X := Xᶜ.Finite
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := by rw [Set.compl_univ]; exact Set.finite_empty
  inter_mem := by
    intro X Y _ hX hY _ _
    rw [Set.compl_inter]; exact hX.union hY
  sub_master := fun _ => Set.subset_univ _

end DomainTheory.NeighbourhoodSystems.Exercise220
