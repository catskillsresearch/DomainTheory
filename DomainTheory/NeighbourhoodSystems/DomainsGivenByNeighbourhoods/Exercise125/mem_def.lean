/-ai
A set belongs to the final-segment system if and only if it is nonempty and an upper set.

The equivalence holds by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.UpperLower.Basic
import all Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Bounds.Basic
import all Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.finalSegmentSystem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

@[simp] theorem mem_def {X : Set Δ} :
    (finalSegmentSystem Δ).mem X ↔ X.Nonempty ∧ IsUpperSet X := Iff.rfl

end FinalSegment

end DomainTheory.NeighbourhoodSystems
