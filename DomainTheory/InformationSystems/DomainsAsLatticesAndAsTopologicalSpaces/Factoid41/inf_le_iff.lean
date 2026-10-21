/-ai
An element lies below a meet if and only if it lies below both arguments.

A lower bound of the meet is a lower bound of each argument by transitivity with the left and right inequalities. A common lower bound of the two arguments is a lower bound of the meet by the universal property.
ai-/
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
