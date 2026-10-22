module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂


variable {α : Type*} {D : NeighborhoodSystem α}


variable (u : D.Element) (hu : u ≠ D.bot)


theorem a_bot : (a u).toElementMap D.bot = D.bot := by
  apply Element.ext
  intro Z
  rw [mem_toElementMap_a, mem_bot]
  exact ⟨fun ⟨_, h⟩ => h.resolve_right (fun h' => h'.1 rfl) |>.symm ▸ rfl,
    fun h => ⟨h ▸ D.master_mem, Or.inl h⟩⟩

end DomainTheory.NeighbourhoodSystems
