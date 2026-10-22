module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.botElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mem_empty_iff_eq_top
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.element_eq_bot_or_top

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Extensionality for `|𝒪|`.** Two elements agreeing on membership of `∅` are equal (it
distinguishes `⊥` from `⊤`). -/
theorem O_ext {z w : O.Element} (h : z.mem ∅ ↔ w.mem ∅) : z = w := by
  by_cases hz : z.mem ∅
  · rw [(mem_empty_iff_eq_top z).mp hz, (mem_empty_iff_eq_top w).mp (h.mp hz)]
  · have ez : z = botElt :=
      (element_eq_bot_or_top z).resolve_right (fun c => hz ((mem_empty_iff_eq_top z).mpr c))
    have ew : w = botElt :=
      (element_eq_bot_or_top w).resolve_right
        (fun c => (fun c' => hz (h.mpr c')) ((mem_empty_iff_eq_top w).mpr c))
    rw [ez, ew]

end DomainTheory.NeighbourhoodSystems.Exercise215
