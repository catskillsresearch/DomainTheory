module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

/-- **Exercise 1.26 — the basic neighbourhood `I(F)`.** `I(F) = {G ∣ F ⊆ ⟨G⟩}`, the finite sets `G`
whose generated ideal contains `F`. -/
def IFamily (F : Finset A) : Set (Finset A) := {G | (↑F : Set A) ⊆ Ideal.span (↑G : Set A)}

end Ring

end DomainTheory.NeighbourhoodSystems
