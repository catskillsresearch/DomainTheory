/-ai
The map associated with an element sends the bottom element to bottom.

Extensionality of elements, after rewriting by the membership criterion of the map and by membership at bottom, leaves a disjunction. The right branch asks bottom to differ from bottom, so the neighbourhood equals the master and therefore belongs to bottom. Conversely, a neighbourhood of bottom is the master, which belongs to the system and is the left branch.
ai-/
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
