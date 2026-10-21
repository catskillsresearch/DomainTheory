/-ai
The right argument of a binary join lies below the join, when the union of the carriers is finitely consistent.

A token of the right argument lies in the union, and a finitely consistent set is contained in its deductive closure.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.Basic
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.subset_deductiveClosure

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)







theorem le_join_right (x y : sys.Element)
    (h : sys.IsFinitelyConsistent (x.carrier ∪ y.carrier)) : y ≤ sys.join x y h :=
  fun _a ha => sys.subset_deductiveClosure _ h (Or.inr ha)

end InfoSys
end DomainTheory.InformationSystems
