/-ai
On the Tarski fixed set, Tarski's map agrees with the first injection.

The conditional reduces to the membership branch.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbSet
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbFun

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise424

open DomainTheory.NeighbourhoodSystems.Exercise414 Function

variable {A B : Type*} {f : A → B} {g : B → A}

theorem sbFun_mem {a : A} (ha : a ∈ sbSet f g) : sbFun f g a = f a := dite_eq_left ha

end DomainTheory.NeighbourhoodSystems.Exercise424
