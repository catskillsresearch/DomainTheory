module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.mem_upSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet_subset_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.20 — the power system `𝒟' = {↑X ∣ X ∈ 𝒟}`** over the tokens `Δ' = 𝒟`. The
master is `↑Δ`; the intersection law uses the consistency witness `Z ∈ ↑Z ⊆ ↑X ∩ ↑Y` to get
`Z ⊆ X ∩ Y`, hence `X ∩ Y ∈ 𝒟` and `↑X ∩ ↑Y = ↑(X∩Y)`. -/
def powerSystem : NeighborhoodSystem (Set α) where
  mem S := ∃ X, V.mem X ∧ S = V.upSet X
  master := V.upSet V.master
  master_nonempty := ⟨V.master, V.master_mem, subset_rfl⟩
  master_mem := ⟨V.master, V.master_mem, rfl⟩
  inter_mem := by
    rintro S T W ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩ ⟨Z, hZ, rfl⟩ hWsub
    have hZin : Z ∈ V.upSet X ∩ V.upSet Y := hWsub ⟨hZ, subset_rfl⟩
    obtain ⟨⟨_, hZX⟩, _, hZY⟩ := hZin
    have hXY : V.mem (X ∩ Y) := V.inter_mem hX hY hZ (Set.subset_inter hZX hZY)
    exact ⟨X ∩ Y, hXY, V.upSet_inter X Y⟩
  sub_master := by
    intro S hS
    obtain ⟨X, hX, rfl⟩ := hS
    exact (V.upSet_subset_iff hX).mpr (V.sub_master hX)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
