module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.inf
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.le_inf

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem inf_le_iff {x y z : sys.Element} : z ≤ sys.inf x y ↔ z ≤ x ∧ z ≤ y :=
  ⟨fun h => ⟨le_trans h (inf.le_left sys x y), le_trans h (inf.le_right sys x y)⟩,
   fun ⟨hx, hy⟩ => sys.le_inf hx hy⟩

end InfoSys
end DomainTheory.InformationSystems
