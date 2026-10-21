/-ai
Applying the K combinator first to an element and then to a second element returns the first element.

Rewrite by the one-argument application of K, then apply beta reduction for the constant function with that value.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















theorem Kcomb_app2 (x y : Pomega) : funOf (funOf Kcomb x) y = x := by
  rw [Kcomb_app]
  exact beta (const_isScottContinuous x) y

end DomainTheory.DataTypesAsLattices
