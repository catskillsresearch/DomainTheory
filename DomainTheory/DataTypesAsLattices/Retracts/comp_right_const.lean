/-ai
For a fixed right argument a, composition on the right with a is Scott continuous in the left argument.

Continuity of forming a graph in a parameter reduces the claim to Scott continuity of application in the function argument, taken at the application of a.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






































theorem comp_right_const (a : Pomega) :
    IsScottContinuous (fun u => comp u a) :=
  graph_const_isScottContinuous (fun u x => funOf u (funOf a x))
    (fun x => funOf_isScottContinuous_left (funOf a x))

end DomainTheory.DataTypesAsLattices
