/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
