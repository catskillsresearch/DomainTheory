/-ai
The omega combinator is Scott continuous.

This is graph continuity for the body that applies the functional to a self-application, using continuity of application in the function argument.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem omegaComb_isScottContinuous : IsScottContinuous omegaComb :=
  graph_const_isScottContinuous
    (fun u x => funOf u (funOf x x))
    (fun x => funOf_isScottContinuous_left (funOf x x))

end DomainTheory.DataTypesAsLattices
