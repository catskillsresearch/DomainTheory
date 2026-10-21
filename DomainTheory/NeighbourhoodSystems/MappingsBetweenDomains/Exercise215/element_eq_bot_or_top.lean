/-ai
Every element of the domain of O is the bottom element or the top element.

If the element contains the empty set, it is the top element. Otherwise the two elements contain the same neighbourhoods. A neighbourhood of the given element is the universe or the empty set: the universe belongs to the bottom element, and the empty set was excluded. A neighbourhood of the bottom element is the master neighbourhood, which belongs to every element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.topElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.botElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mem_botElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mem_empty_iff_eq_top

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Two elements.** Every element of `|𝒪|` is `⊥` or `⊤`. -/
theorem element_eq_bot_or_top (z : O.Element) : z = botElt ∨ z = topElt := by
  by_cases hz : z.mem ∅
  · exact Or.inr ((mem_empty_iff_eq_top z).mp hz)
  · refine Or.inl ?_
    apply Element.ext
    intro Y
    constructor
    · intro hY
      rcases (O_mem.mp (z.sub hY)) with rfl | rfl
      · exact mem_botElt.mpr rfl
      · exact absurd hY hz
    · intro hY
      rw [mem_botElt.mp hY, ← O_master]
      exact z.master_mem

end DomainTheory.NeighbourhoodSystems.Exercise215
