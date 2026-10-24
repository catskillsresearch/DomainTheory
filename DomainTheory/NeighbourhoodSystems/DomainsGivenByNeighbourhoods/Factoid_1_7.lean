module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_5

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L267 FACTOID 1.7a2 inclusion-reversing principals -/
/- concordance: source L264 FACTOID 1.7a1 principals are one-one -/
/-- **Factoid 1.7a (Scott 1981, PRG-19) — inclusion-*reversing*.** "It is obvious that the
correspondence between `X` and `↑X` is one-one and inclusion *reversing*." The order on `↑`:
`↑X ⊑ ↑Y ↔ Y ⊆ X` (equivalently Scott's `X ⊆ Y ↔ ↑Y ⊑ ↑X`).

`→` tests at `Z = X` (`X ∈ ↑X` since `X ⊆ X`), reading off `Y ⊆ X` from `X ∈ ↑Y`; `←` chains
`Y ⊆ X ⊆ Z`. -/
theorem principal_le_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.principal hX ≤ V.principal hY ↔ Y ⊆ X := by
  constructor
  · intro h
    exact (h X ⟨hX, subset_rfl⟩).2
  · intro hYX Z hZ
    exact ⟨hZ.1, hYX.trans hZ.2⟩

/-- **Factoid 1.7a (Scott 1981, PRG-19) — one-one.** The correspondence `X ↦ ↑X` is injective:
`↑X = ↑Y ⟹ X = Y`. Antisymmetry applied to `principal_le_iff` in both directions. -/
theorem principal_injective {X Y : Set α} (hX : V.mem X) (hY : V.mem Y)
    (h : V.principal hX = V.principal hY) : X = Y := by
  have hYX : Y ⊆ X := (V.principal_le_iff hX hY).mp (le_of_eq h)
  have hXY : X ⊆ Y := (V.principal_le_iff hY hX).mp (le_of_eq h.symm)
  exact Set.Subset.antisymm hXY hYX

/- concordance: source L273 FACTOID 1.7b union of principal filters -/
/-- **Factoid 1.7b (Scott 1981, PRG-19).** "It is also obvious from the definitions that for each
`x ∈ |𝒟|`, `x = ⋃ {↑X ∣ X ∈ x}`." In membership form (the union over a `Set (Set α)` made
concrete): a neighbourhood `Z` is in `x` iff `Z` lies in the principal filter `↑X` of *some*
member `X` of `x`.

`→` uses `X = Z` (`Z ∈ ↑Z` as `Z ⊆ Z`); `←` is upward closure `up_mem` (`X ⊆ Z`, `Z ∈ 𝒟`). -/
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
