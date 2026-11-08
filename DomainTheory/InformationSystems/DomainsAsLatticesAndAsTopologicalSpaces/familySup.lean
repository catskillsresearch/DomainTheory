module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.deductiveClosure

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

def familyUnionCarrier (S : Set sys.Element) : Set α :=
  {a | ∃ x ∈ S, a ∈ x.carrier}

theorem finitelyConsistent_of_upperBound (S : Set sys.Element) {z : sys.Element}
    (h : ∀ x ∈ S, x ≤ z) : sys.IsFinitelyConsistent (sys.familyUnionCarrier S) := by
  intro Y hY
  have hYZ : (Y : Set α) ⊆ z.carrier := by
    intro a ha
    obtain ⟨x, hx, ha'⟩ := hY ha
    exact h x hx ha'
  exact z.consistent Y hYZ

def familySup (S : Set sys.Element)
    (hU : sys.IsFinitelyConsistent (sys.familyUnionCarrier S)) : sys.Element :=
  sys.deductiveClosure (sys.familyUnionCarrier S) hU

namespace familySup

theorem le (S : Set sys.Element)
    (hU : sys.IsFinitelyConsistent (sys.familyUnionCarrier S)) {z : sys.Element}
    (h : ∀ x ∈ S, x ≤ z) : sys.familySup S hU ≤ z := by
  intro a ha
  obtain ⟨u, huU, hEnt⟩ := ha
  have huZ : (u : Set α) ⊆ z.carrier := by
    intro b hb
    obtain ⟨x, hx, hb'⟩ := huU hb
    exact h x hx hb'
  exact z.closed u a huZ hEnt

theorem le_of_mem (S : Set sys.Element)
    (hU : sys.IsFinitelyConsistent (sys.familyUnionCarrier S)) {x : sys.Element}
    (hx : x ∈ S) : x ≤ sys.familySup S hU := by
  intro a ha
  exact deductiveClosure.subset sys _ hU ⟨x, hx, ha⟩

theorem exists_isLUB_iff (S : Set sys.Element) :
    (∃ z : sys.Element, (∀ x ∈ S, x ≤ z) ∧ ∀ w, (∀ x ∈ S, x ≤ w) → z ≤ w) ↔
      Nonempty (sys.IsFinitelyConsistent (sys.familyUnionCarrier S)) := by
  constructor
  · rintro ⟨z, hub, _⟩
    exact ⟨sys.finitelyConsistent_of_upperBound S hub⟩
  · rintro ⟨hU⟩
    refine ⟨sys.familySup S hU, fun x hx => le_of_mem sys S hU hx,
      fun w hw => le sys S hU hw⟩

end familySup

end InfoSys
end DomainTheory.InformationSystems
