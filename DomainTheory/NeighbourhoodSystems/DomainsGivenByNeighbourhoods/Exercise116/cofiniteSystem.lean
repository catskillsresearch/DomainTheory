/-ai
The cofinite neighbourhood system on the natural numbers takes as neighbourhoods the sets whose complements are finite, with the whole set as master neighbourhood. The complement of the master is empty, hence finite. The complement of an intersection is the union of the complements, so the intersection of two neighbourhoods is a neighbourhood. Every neighbourhood is contained in the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

/-- **Exercise 1.16 — the cofinite neighbourhood system on `ℕ`.** `X ∈ 𝒟 ⟺ Xᶜ` finite;
closed under finite intersection since `(X∩Y)ᶜ = Xᶜ ∪ Yᶜ`. -/
def cofiniteSystem : NeighborhoodSystem ℕ where
  mem X := Xᶜ.Finite
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := by rw [Set.compl_univ]; exact Set.finite_empty
  inter_mem := by
    intro X Y _ hX hY _ _
    rw [Set.compl_inter]
    exact hX.union hY
  sub_master := fun _ => Set.subset_univ _

end Cofinite

end DomainTheory.NeighbourhoodSystems
