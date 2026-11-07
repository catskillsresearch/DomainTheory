module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.subdomain

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Set

variable {α : Type*}

/-- Scott's Definition 6.10: `D ◁ E` — same tokens, fewer neighbourhoods, inherited consistency. -/
theorem definition_610 {D E : NeighborhoodSystem α} :
    D ◁ E ↔
      D.master = E.master ∧
        (∀ {X}, D.mem X → E.mem X) ∧
          (∀ {X Y}, D.mem X → D.mem Y → E.mem (X ∩ Y) → D.mem (X ∩ Y)) :=
  ⟨fun h => ⟨h.master_eq, h.sub, h.inter_closed⟩,
    fun ⟨hm, hsub, hinter⟩ => ⟨hm, hsub, hinter⟩⟩

end DomainTheory.NeighbourhoodSystems
