module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.IsFinitelyConsistent
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.deductiveClosure
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.familyUnionCarrier
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.familySup
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.join
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.exists_entSet_of_subset_deductive
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.le_join_left
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.le_join_right

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem exists_join_iff (x y : sys.Element) :
    (∃ z : sys.Element, x ≤ z ∧ y ≤ z) ↔
      Nonempty (sys.IsFinitelyConsistent (x.carrier ∪ y.carrier)) := by
  constructor
  · rintro ⟨z, hx, hy⟩
    exact ⟨fun Y hY => z.consistent Y (fun a ha => by
      rcases hY ha with h | h
      · exact hx h
      · exact hy h)⟩
  · rintro ⟨h⟩
    exact ⟨sys.join x y h, sys.le_join_left x y h, sys.le_join_right x y h⟩

end InfoSys
end DomainTheory.InformationSystems
