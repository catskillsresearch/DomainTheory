/-ai
A set of elements of Pω is Σ¹₁ when two Scott-continuous maps f and g cut it out by the condition that for the element x there exists y such that the functions coded by f(x) and g(x) agree at y.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def IsSigma11 (U : Set Pomega) : Prop :=
  ∃ f g, IsScottContinuous f ∧ IsScottContinuous g ∧
    U = {x | ∃ y, funOf (f x) y = funOf (g x) y}

end DomainTheory.DataTypesAsLattices
