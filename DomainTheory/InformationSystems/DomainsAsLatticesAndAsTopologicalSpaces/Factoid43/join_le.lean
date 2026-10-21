/-ai
The binary join of two elements lies below any common upper bound.

A token of the join is entailed by a finite set contained in the union of the carriers. Each token of that finite set lies in one of the two elements and therefore in the upper bound, and closure of the upper bound under entailment contains the original token.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem join_le (x y z : sys.Element)
    (h : sys.IsFinitelyConsistent (x.carrier ∪ y.carrier))
    (hx : x ≤ z) (hy : y ≤ z) : sys.join x y h ≤ z := by
  intro a ha
  obtain ⟨u, huU, hEnt⟩ := ha
  have huZ : (u : Set α) ⊆ z.carrier := by
    intro b hb
    rcases huU hb with hb' | hb'
    · exact hx hb'
    · exact hy hb'
  exact z.closed u a huZ hEnt

end InfoSys
end DomainTheory.InformationSystems
