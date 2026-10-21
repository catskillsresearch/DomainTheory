/-ai
A neighbourhood belongs to the n-th approximant of an approximable endomap if and only if the n-th iterate relates the master neighbourhood to it.

In one direction the witnessing neighbourhood lies in the bottom element, hence is the master, and the relation is already from the master. In the other direction the master belongs to the bottom element and is the witness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap
















/-- `Y ∈ fⁿ(⊥) ↔ Δ fⁿ Y`: the `n`-th approximant is the family of neighbourhoods reachable from
`Δ` in exactly the `n` steps recorded by `fⁿ`. -/
theorem mem_iterElem (f : ApproximableMap V V) (n : ℕ) {X : Set α} :
    (f.iterElem n).mem X ↔ (f.iterMap n).rel V.master X := by
  constructor
  · rintro ⟨W, hW, hWX⟩
    rw [mem_bot] at hW; subst hW; exact hWX
  · intro h; exact ⟨V.master, by rw [mem_bot], h⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
