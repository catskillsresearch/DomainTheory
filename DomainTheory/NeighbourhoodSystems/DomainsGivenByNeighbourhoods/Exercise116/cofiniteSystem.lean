module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic

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
