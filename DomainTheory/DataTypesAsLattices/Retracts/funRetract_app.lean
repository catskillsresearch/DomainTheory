/-ai
Applying the function retract to u returns the graph of application of u.

This is β-conversion. Continuity of graph formation, using Scott continuity of application in the function argument, supplies the continuity hypothesis.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem funRetract_app (u : Pomega) :
    funOf funRetract u = graph (fun x => funOf u x) :=
  beta (graph_const_isScottContinuous (fun u x => funOf u x)
    (fun x => funOf_isScottContinuous_left x)) u

end DomainTheory.DataTypesAsLattices
