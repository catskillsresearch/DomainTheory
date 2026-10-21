/-ai
The map sending a function to the graph of a second function mapped to the graph of their pointwise application is Scott continuous.

Two applications of the constant-graph lemma. Continuity in the outer function of the innermost body is substitution of application at the inner value into application at the argument.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Scomb_map_isScottContinuous :
    IsScottContinuous (fun u => graph (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x)))) :=
  graph_const_isScottContinuous
    (fun u v => graph (fun x => funOf (funOf u x) (funOf v x)))
    (fun v =>
      graph_const_isScottContinuous
        (fun u x => funOf (funOf u x) (funOf v x))
        (fun x =>
          theorem_1_3
            (f := fun t => funOf t (funOf v x))
            (g := fun u => funOf u x)
            (funOf_isScottContinuous_left (funOf v x))
            (funOf_isScottContinuous_left x)))

end DomainTheory.DataTypesAsLattices
