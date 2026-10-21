/-ai
Applying the operator HF at an interpreter to an environment yields the graph of one step of that interpreter in the term.

This is beta reduction for the inner Scott-continuous map.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.HF_inner_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem HF_app (H e : Pomega) :
    funOf (HF H) e = graph (fun t => Hstep H e t) :=
  beta (HF_inner_isScottContinuous H) e

end DomainTheory.DataTypesAsLattices
