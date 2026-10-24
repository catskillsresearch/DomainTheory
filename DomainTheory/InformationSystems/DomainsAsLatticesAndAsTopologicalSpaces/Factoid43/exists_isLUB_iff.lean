module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.Basic
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.le_familySup
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.familySup
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.finitelyConsistent_of_upperBound

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- Join exists iff the union is finitely consistent. -/
theorem exists_isLUB_iff (S : Set sys.Element) :
    (∃ z : sys.Element, (∀ x ∈ S, x ≤ z) ∧ ∀ w, (∀ x ∈ S, x ≤ w) → z ≤ w) ↔
      Nonempty (sys.IsFinitelyConsistent (sys.familyUnionCarrier S)) := by
  constructor
  · rintro ⟨z, hub, _⟩
    exact ⟨sys.finitelyConsistent_of_upperBound S hub⟩
  · rintro ⟨hU⟩
    refine ⟨sys.familySup S hU, fun x hx => sys.le_familySup S hU hx,
      fun w hw => familySup.le sys S hU hw⟩

end InfoSys
end DomainTheory.InformationSystems
