/-ai
An approximable endomap is a finitary projection if and only if a neighbourhood belongs to the image of an element exactly when it is a neighbourhood and some neighbourhood of the element is contained in it and related to itself by the map.

One direction is the derivation of the step-closure formula from a finitary projection, and the other is the derivation of a finitary projection from that formula.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.isFinitaryProjection_of_formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.formula_of_isFinitaryProjection

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}


/-- **Theorem 8.5 (Scott 1981, PRG-19), in full.** `a : E → E` is a finitary projection iff it
satisfies the step-closure formula `a(x) = {Y ∈ E ∣ ∃X∈x, X⊆Y ∧ XaX}` for every `x ∈ |E|`. -/
theorem finitaryProjection_iff_formula (a : ApproximableMap E E) :
    FinitaryProjection a ↔ ∀ (x : E.Element) {Y : Set α}, (a.toElementMap x).mem Y ↔
      E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X :=
  ⟨fun h => formula_of_isFinitaryProjection h, fun hii => isFinitaryProjection_of_formula a hii⟩

end DomainTheory.NeighbourhoodSystems
