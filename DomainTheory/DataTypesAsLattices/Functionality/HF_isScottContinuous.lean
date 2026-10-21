/-ai
The operator HF is Scott continuous in the interpreter.

Two applications of the constant-graph lemma, using continuity of the step in the interpreter.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep_isScottContinuous_H

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem HF_isScottContinuous : IsScottContinuous HF :=
  graph_const_isScottContinuous
    (fun H e => graph (fun t => Hstep H e t))
    (fun e => graph_const_isScottContinuous (fun H t => Hstep H e t)
      (fun t => Hstep_isScottContinuous_H e t))

end DomainTheory.DataTypesAsLattices
