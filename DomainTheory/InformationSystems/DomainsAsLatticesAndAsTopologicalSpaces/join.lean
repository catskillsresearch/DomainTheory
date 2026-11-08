module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.deductiveClosure

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

def join (x y : sys.Element)
    (h : sys.IsFinitelyConsistent (x.carrier ∪ y.carrier)) : sys.Element :=
  sys.deductiveClosure (x.carrier ∪ y.carrier) h

namespace join

theorem le (x y z : sys.Element)
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

theorem le_left (x y : sys.Element)
    (h : sys.IsFinitelyConsistent (x.carrier ∪ y.carrier)) : x ≤ sys.join x y h :=
  fun _a ha => deductiveClosure.subset sys _ h (Or.inl ha)

theorem le_right (x y : sys.Element)
    (h : sys.IsFinitelyConsistent (x.carrier ∪ y.carrier)) : y ≤ sys.join x y h :=
  fun _a ha => deductiveClosure.subset sys _ h (Or.inr ha)

theorem exists_iff (x y : sys.Element) :
    (∃ z : sys.Element, x ≤ z ∧ y ≤ z) ↔
      Nonempty (sys.IsFinitelyConsistent (x.carrier ∪ y.carrier)) := by
  constructor
  · rintro ⟨z, hx, hy⟩
    exact ⟨fun Y hY => z.consistent Y (fun a ha => by
      rcases hY ha with h | h
      · exact hx h
      · exact hy h)⟩
  · rintro ⟨h⟩
    exact ⟨sys.join x y h, le_left sys x y h, le_right sys x y h⟩

end join

end InfoSys
end DomainTheory.InformationSystems
