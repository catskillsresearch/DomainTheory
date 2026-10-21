/-ai
For a fixed interpreter, the map sending an environment to the graph of one step in the term is Scott continuous.

This is the constant-graph lemma, using continuity of the step in the environment.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep_isScottContinuous_e

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem HF_inner_isScottContinuous (H : Pomega) :
    IsScottContinuous (fun e => graph (fun t => Hstep H e t)) :=
  graph_const_isScottContinuous (fun e t => Hstep H e t)
    (fun t => Hstep_isScottContinuous_e H t)

end DomainTheory.DataTypesAsLattices
