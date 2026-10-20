module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}





/-- **Element-wise description of `i` (Scott's equation).** `i(x) = {Y ∈ E ∣ ∃ X ∈ x, X ⊆ Y}`. -/
theorem toElementMap_inj (h : D ◁ E) (x : D.Element) {Y : Set α} :
    (h.inj.toElementMap x).mem Y ↔ E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y := by
  constructor
  · rintro ⟨X, hX, _, hY, hXY⟩
    exact ⟨hY, X, hX, hXY⟩
  · rintro ⟨hY, X, hX, hXY⟩
    exact ⟨X, hX, x.sub hX, hY, hXY⟩

end Subsystem
end DomainTheory.NeighbourhoodSystems
