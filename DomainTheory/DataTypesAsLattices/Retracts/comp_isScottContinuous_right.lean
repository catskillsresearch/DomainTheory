/-ai
For a fixed left argument u, composition with u is Scott continuous in the right argument.

Continuity of forming a graph in a parameter reduces the claim to continuity of the substituted application. Theorem 1.3 substitutes application of u into application in the function argument.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem comp_isScottContinuous_right (u : Pomega) :
    IsScottContinuous (fun v => comp u v) :=
  graph_const_isScottContinuous (fun v x => funOf u (funOf v x))
    (fun x => theorem_1_3 (funOf_isScottContinuous u) (funOf_isScottContinuous_left x))

end DomainTheory.DataTypesAsLattices
