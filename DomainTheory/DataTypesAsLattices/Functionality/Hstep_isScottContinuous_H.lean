/-ai
For a fixed expression and environment, the interpreter step is Scott continuous in the interpreter.

The argument is a nest of ternary continuity for the definite conditional. The tag tests and the variable and zero clauses are constant in the interpreter. The successor, predecessor, conditional, application, and abstraction clauses are continuous in the interpreter, and the final alternative is the constant top element.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.hSucc_isScottContinuous_H
public import DomainTheory.DataTypesAsLattices.Functionality.hPred_isScottContinuous_H
public import DomainTheory.DataTypesAsLattices.Functionality.hCond_isScottContinuous_H
public import DomainTheory.DataTypesAsLattices.Functionality.hApp_isScottContinuous_H
public import DomainTheory.DataTypesAsLattices.Functionality.hLam_isScottContinuous_H

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Hstep_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => Hstep H e t) :=
  continuous_nary
    (fun y z => dcondSet_isScottContinuous_left y z)
    (fun x z => dcondSet_isScottContinuous_mid x z)
    (fun x y => dcondSet_isScottContinuous_right x y)
    (const_isScottContinuous (expTag e)) (const_isScottContinuous (hVar e t))
    (continuous_nary
      (fun y z => dcondSet_isScottContinuous_left y z)
      (fun x z => dcondSet_isScottContinuous_mid x z)
      (fun x y => dcondSet_isScottContinuous_right x y)
      (const_isScottContinuous (predSet (expTag e)))
      (const_isScottContinuous hZero)
      (continuous_nary
        (fun y z => dcondSet_isScottContinuous_left y z)
        (fun x z => dcondSet_isScottContinuous_mid x z)
        (fun x y => dcondSet_isScottContinuous_right x y)
        (const_isScottContinuous (predSet (predSet (expTag e))))
        (hSucc_isScottContinuous_H e t)
        (continuous_nary
          (fun y z => dcondSet_isScottContinuous_left y z)
          (fun x z => dcondSet_isScottContinuous_mid x z)
          (fun x y => dcondSet_isScottContinuous_right x y)
          (const_isScottContinuous (predSet^[3] (expTag e)))
          (hPred_isScottContinuous_H e t)
          (continuous_nary
            (fun y z => dcondSet_isScottContinuous_left y z)
            (fun x z => dcondSet_isScottContinuous_mid x z)
            (fun x y => dcondSet_isScottContinuous_right x y)
            (const_isScottContinuous (predSet^[4] (expTag e)))
            (hCond_isScottContinuous_H e t)
            (continuous_nary
              (fun y z => dcondSet_isScottContinuous_left y z)
              (fun x z => dcondSet_isScottContinuous_mid x z)
              (fun x y => dcondSet_isScottContinuous_right x y)
              (const_isScottContinuous (predSet^[5] (expTag e)))
              (hApp_isScottContinuous_H e t)
              (continuous_nary
                (fun y z => dcondSet_isScottContinuous_left y z)
                (fun x z => dcondSet_isScottContinuous_mid x z)
                (fun x y => dcondSet_isScottContinuous_right x y)
                (const_isScottContinuous (predSet^[6] (expTag e)))
                (hLam_isScottContinuous_H e t)
                (const_isScottContinuous topElem)))))))

end DomainTheory.DataTypesAsLattices
