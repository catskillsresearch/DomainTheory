module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.Basic
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.inf_le_left
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.inf_le_right
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.le_inf

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- Meet is the greatest lower bound. -/
theorem inf_le_iff {x y z : sys.Element} : z ≤ sys.inf x y ↔ z ≤ x ∧ z ≤ y :=
  ⟨fun h => ⟨le_trans h (sys.inf_le_left x y), le_trans h (sys.inf_le_right x y)⟩,
   fun ⟨hx, hy⟩ => sys.le_inf hx hy⟩

end InfoSys
end DomainTheory.InformationSystems
