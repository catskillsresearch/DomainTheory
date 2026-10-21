/-ai
Applying the K combinator to an element yields the graph of the constant function with that value.

This is beta reduction for the constant-graph map that returns its function argument, which is continuous because the identity is continuous.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Kcomb_app (x : Pomega) :
    funOf Kcomb x = graph (fun _ => x) :=
  beta (graph_const_isScottContinuous (fun x _ => x)
    (fun _ => id_isScottContinuous)) x

end DomainTheory.DataTypesAsLattices
