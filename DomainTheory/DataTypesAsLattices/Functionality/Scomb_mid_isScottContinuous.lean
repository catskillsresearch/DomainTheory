/-ai
For a fixed function, the map sending a second function to the graph of their pointwise application is Scott continuous.

The constant-graph lemma, whose body is substitution of application of the fixed function into application at the argument.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Scomb_mid_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x))) :=
  graph_const_isScottContinuous
    (fun v x => funOf (funOf u x) (funOf v x))
    (fun x =>
      theorem_1_3 (funOf_isScottContinuous (funOf u x))
        (funOf_isScottContinuous_left x))

end DomainTheory.DataTypesAsLattices
