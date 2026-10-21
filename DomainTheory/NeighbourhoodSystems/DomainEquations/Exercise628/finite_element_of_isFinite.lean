/-ai
If a neighbourhood system has finitely many neighbourhoods, then its element domain is finite.

The neighbourhood subtype is finite by hypothesis. Sending an element to the set of neighbourhoods it contains injects the element domain into the powerset of that subtype. Two elements with the same image agree on every token set: when the set is a neighbourhood, extensionality of the images gives the same membership, and when it is not a neighbourhood, neither element contains it, since containment would force the set to be a neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise628.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}







/-- **A finite system has a finite element domain.** A filter `x : |D|` is determined by which of
the (finitely many) neighbourhoods it contains, so `x ↦ {p | x.mem p.1}` injects `|D|` into the
finite powerset `Set {X // D.mem X}`. -/
theorem finite_element_of_isFinite {α : Type*} {D : NeighborhoodSystem α} (h : D.IsFinite) :
    Finite D.Element := by
  have : Finite {X : Set α // D.mem X} := h
  apply Finite.of_injective
    (β := Set {X : Set α // D.mem X}) (fun x => {p | x.mem p.1})
  intro x y hxy
  apply Element.ext
  intro X
  by_cases hX : D.mem X
  · have := Set.ext_iff.mp hxy ⟨X, hX⟩
    simpa using this
  · exact ⟨fun hmem => absurd (x.sub hmem) hX, fun hmem => absurd (y.sub hmem) hX⟩

end DomainTheory.NeighbourhoodSystems
