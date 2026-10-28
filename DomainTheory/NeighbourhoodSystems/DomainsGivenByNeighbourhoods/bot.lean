module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.principal

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

def bot : V.Element := V.principal V.master_mem

@[simp] theorem mem_bot {Y : Set α} : V.bot.mem Y ↔ Y = V.master := by
  constructor
  · rintro ⟨hY, hΔY⟩
    exact Set.Subset.antisymm (V.sub_master hY) hΔY
  · rintro rfl
    exact ⟨V.master_mem, subset_rfl⟩
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
