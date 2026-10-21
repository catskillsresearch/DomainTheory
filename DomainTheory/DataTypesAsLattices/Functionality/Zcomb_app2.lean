/-ai
Applying the combinator Z at a stage first to a function and then to a value yields the iterator of that function at that value.

Rewrite by the one-argument application, then apply beta reduction for continuity of the iterator in the value.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Z_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Functionality.Zcomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
























theorem Zcomb_app2 (n : ℕ) (f x : Pomega) :
    funOf (funOf (Zcomb n) f) x = Z n f x := by
  rw [Zcomb_app]
  exact beta (Z_isScottContinuous_right n f) x

end DomainTheory.DataTypesAsLattices
