
module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45.finiteApproximants

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.closures_directed
@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem directed_finiteApproximants (x : sys.Element) :
    sys.IsDirected (sys.finiteApproximants x) := by
  intro y₁ y₂ hy₁ hy₂
  obtain ⟨u, hu, huX, rfl⟩ := hy₁
  obtain ⟨v, hv, hvX, rfl⟩ := hy₂
  obtain ⟨w, hw, hwX, huw, hvw⟩ := sys.closures_directed x hu hv huX hvX
  exact ⟨sys.closure w hw, ⟨w, hw, hwX, rfl⟩, huw, hvw⟩

end InfoSys
end DomainTheory.InformationSystems
