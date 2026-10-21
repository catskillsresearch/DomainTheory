/-ai
Applying the S combinator first to one function and then to another yields the graph of the pointwise application of the first to the second.

Rewrite by the one-argument application, then apply beta reduction for continuity of the middle map.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_mid_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















theorem Scomb_app2 (f g : Pomega) :
    funOf (funOf Scomb f) g =
      graph (fun x => funOf (funOf f x) (funOf g x)) := by
  rw [Scomb_app]
  exact beta (Scomb_mid_isScottContinuous f) g

end DomainTheory.DataTypesAsLattices
