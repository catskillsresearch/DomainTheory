/-ai
Tarski's map sends an element of the fixed set to its image under the first injection, and sends an element outside the fixed set to a chosen preimage under the second injection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbSet
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.mem_range_of_not_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise424

open DomainTheory.NeighbourhoodSystems.Exercise414 Function

variable {A B : Type*} {f : A → B} {g : B → A}

open Classical in
/-- **Exercise 4.24 (Scott 1981, PRG-19).** Tarski's bijection `h : A → B`: `f` on the fixed set
`X`, and the `g`-inverse off it. -/
noncomputable def sbFun (f : A → B) (g : B → A) (a : A) : B :=
  if ha : a ∈ sbSet f g then f a else Classical.choose (mem_range_of_not_mem ha)

end DomainTheory.NeighbourhoodSystems.Exercise424
