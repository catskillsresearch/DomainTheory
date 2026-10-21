/-ai
For fixed u and v, the map sending x to the application of u at x applied to v at x is Scott continuous.

The tuple form of Theorem 1.3 combines left continuity of application, continuity of application, continuity of application of u, and continuity of application of v.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem Scomb_inner_cont (u v : Pomega) :
    IsScottContinuous (fun x => funOf (funOf u x) (funOf v x)) :=
  theorem_1_3_tuple
    (fun y => funOf_isScottContinuous_left y)
    (fun t => funOf_isScottContinuous t)
    (funOf_isScottContinuous u)
    (funOf_isScottContinuous v)

end DomainTheory.DataTypesAsLattices
