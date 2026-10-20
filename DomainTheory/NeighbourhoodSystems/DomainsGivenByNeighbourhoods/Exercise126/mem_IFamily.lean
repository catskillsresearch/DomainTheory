module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.RingTheory.Ideal.Span
import all Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

@[simp] theorem mem_IFamily {F G : Finset A} :
    G ∈ IFamily F ↔ (↑F : Set A) ⊆ Ideal.span (↑G : Set A) := Iff.rfl

end Ring

end DomainTheory.NeighbourhoodSystems
