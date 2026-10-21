/-ai
The typical 𝔊 set is Scott open.

The first half of the 𝔊 theorem says that the set of x with 0 in f(x) is Scott open whenever f is Scott continuous. Applied to the identity, this is the set of x with 0 in x.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_1

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem typicalG_isScottOpen : IsScottOpen typicalG :=
  ((theorem_6_1).1 (fun x => x) id_isScottContinuous)

end DomainTheory.DataTypesAsLattices
