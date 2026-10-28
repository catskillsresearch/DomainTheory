module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_5

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

theorem principal_le_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.principal hX ≤ V.principal hY ↔ Y ⊆ X := by
  constructor
  · intro h
    exact (h X ⟨hX, subset_rfl⟩).2
  · intro hYX Z hZ
    exact ⟨hZ.1, hYX.trans hZ.2⟩

theorem principal_injective {X Y : Set α} (hX : V.mem X) (hY : V.mem Y)
    (h : V.principal hX = V.principal hY) : X = Y := by
  have hYX : Y ⊆ X := (V.principal_le_iff hX hY).mp (le_of_eq h)
  have hXY : X ⊆ Y := (V.principal_le_iff hY hX).mp (le_of_eq h.symm)
  exact Set.Subset.antisymm hXY hYX

theorem eq_iUnion_principal (x : V.Element) {Z : Set α} :
    x.mem Z ↔ ∃ X, ∃ hX : x.mem X, (V.principal (x.sub hX)).mem Z := by
  constructor
  · intro hZ
    exact ⟨Z, hZ, x.sub hZ, subset_rfl⟩
  · rintro ⟨X, hX, hVZ, hXZ⟩
    exact x.up_mem hX hVZ hXZ

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end
