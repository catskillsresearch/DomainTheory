/-ai
The typical Bδ set is the set of elements u of Pω such that u applied to the singleton {0} equals u applied to the singleton {1}.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def typicalBdelta : Set Pomega :=
  {u | funOf u (ofNat 0) = funOf u (ofNat 1)}

end DomainTheory.DataTypesAsLattices
