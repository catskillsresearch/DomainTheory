/-ai
For a fixed code and environment, the abstraction clause is Scott-continuous in the candidate.

The proof is Theorem 1.3 of continuity of application of right injection with constancy of graphs under Scott continuity, whose sections are the continuity of the recursive call in the candidate.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.hApply_isScottContinuous_H

@[expose] public section


namespace DomainTheory.DataTypesAsLattices














































theorem hLam_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hLam H e t) :=
  theorem_1_3 (funOf_isScottContinuous inrightC)
    (graph_const_isScottContinuous
      (fun H x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnvUnion t x (funOf (expPayload e) (ofNat 0))))
      (fun _ => hApply_isScottContinuous_H _ _))

end DomainTheory.DataTypesAsLattices
