module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.inf
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.le_inf

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem inf_mono {x₁ x₂ y₁ y₂ : sys.Element} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    sys.inf x₁ y₁ ≤ sys.inf x₂ y₂ :=
  sys.le_inf (le_trans (inf.le_left sys _ _) hx) (le_trans (inf.le_right sys _ _) hy)

end InfoSys
end DomainTheory.InformationSystems
