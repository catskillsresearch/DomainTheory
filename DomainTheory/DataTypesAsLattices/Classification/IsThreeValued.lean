/-ai
An element of Pω is three-valued when it is the bottom element, the singleton of zero, or the top element.
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

def IsThreeValued (x : Pomega) : Prop :=
  x = botElem ∨ x = ofNat 0 ∨ x = topElem

end DomainTheory.DataTypesAsLattices
