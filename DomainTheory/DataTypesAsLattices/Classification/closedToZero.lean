/-ai
The three-valued characteristic of a set C sends each x in Pω to the singleton {0} united with the top characteristic of the complement of C. On a Scott-closed set this returns {0}, and off that set it returns ⊤.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen
public import DomainTheory.DataTypesAsLattices.Classification.charTop

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

/-- Three-valued characteristic of a Scott-closed set: `0` on `C`, `⊤` off `C`. -/
def closedToZero (C : Set Pomega) (x : Pomega) : Pomega :=
  ofNat 0 ∪ charTop Cᶜ x

end DomainTheory.DataTypesAsLattices
