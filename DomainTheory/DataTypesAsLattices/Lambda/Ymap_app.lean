/-ai
If g is Scott continuous in each argument separately, then the application of its parameterized fixed-point map at x is the fixed point of g at x.

This is beta reduction, using Scott continuity of the parameterized fixed point.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.fix_param_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















































theorem Ymap_app {g : Pomega → Pomega → Pomega}
    (hgx : ∀ y, IsScottContinuous (fun x => g x y))
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) (x : Pomega) :
    funOf (Ymap g) x = fix (g x) :=
  beta (fix_param_isScottContinuous hgx hgy) x

end DomainTheory.DataTypesAsLattices
