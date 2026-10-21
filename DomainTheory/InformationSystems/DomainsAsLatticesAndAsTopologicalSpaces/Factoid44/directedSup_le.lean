/-ai
If every member of a nonempty directed family lies below an element, then the directed supremum lies below that element.

Finite consistency of the union of the carriers reduces the inequality to the corresponding inequality for the family supremum.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.Basic

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.familySup_le
@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem directedSup_le (S : Set sys.Element) (hne : S.Nonempty) (hdir : sys.IsDirected S)
    {z : sys.Element} (h : ∀ x ∈ S, x ≤ z) : sys.directedSup S hne hdir ≤ z :=
  sys.familySup_le S (sys.finitelyConsistent_of_directed S hne hdir) h

end InfoSys
end DomainTheory.InformationSystems
