/-ai
For a fixed interpreter and expression, the interpreter step is Scott continuous in the environment.

The argument is a nest of ternary continuity for the definite conditional. The tag tests and the zero clause are constant in the environment. The variable clause and the successor through abstraction clauses are continuous in the environment, and the final alternative is the constant top element.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.hVar_isScottContinuous_t
public import DomainTheory.DataTypesAsLattices.Functionality.hSucc_isScottContinuous_t
public import DomainTheory.DataTypesAsLattices.Functionality.hPred_isScottContinuous_t
public import DomainTheory.DataTypesAsLattices.Functionality.hCond_isScottContinuous_t
public import DomainTheory.DataTypesAsLattices.Functionality.hApp_isScottContinuous_t
public import DomainTheory.DataTypesAsLattices.Functionality.hLam_isScottContinuous_t

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem Hstep_isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => Hstep H e t) :=
  continuous_nary
    (fun y z => dcondSet_isScottContinuous_left y z)
    (fun x z => dcondSet_isScottContinuous_mid x z)
    (fun x y => dcondSet_isScottContinuous_right x y)
    (const_isScottContinuous (expTag e))
    (hVar_isScottContinuous_t e)
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
        (hSucc_isScottContinuous_t H e)
        (continuous_nary
          (fun y z => dcondSet_isScottContinuous_left y z)
          (fun x z => dcondSet_isScottContinuous_mid x z)
          (fun x y => dcondSet_isScottContinuous_right x y)
          (const_isScottContinuous (predSet^[3] (expTag e)))
          (hPred_isScottContinuous_t H e)
          (continuous_nary
            (fun y z => dcondSet_isScottContinuous_left y z)
            (fun x z => dcondSet_isScottContinuous_mid x z)
            (fun x y => dcondSet_isScottContinuous_right x y)
            (const_isScottContinuous (predSet^[4] (expTag e)))
            (hCond_isScottContinuous_t H e)
            (continuous_nary
              (fun y z => dcondSet_isScottContinuous_left y z)
              (fun x z => dcondSet_isScottContinuous_mid x z)
              (fun x y => dcondSet_isScottContinuous_right x y)
              (const_isScottContinuous (predSet^[5] (expTag e)))
              (hApp_isScottContinuous_t H e)
              (continuous_nary
                (fun y z => dcondSet_isScottContinuous_left y z)
                (fun x z => dcondSet_isScottContinuous_mid x z)
                (fun x y => dcondSet_isScottContinuous_right x y)
                (const_isScottContinuous (predSet^[6] (expTag e)))
                (hLam_isScottContinuous_t H e)
                (const_isScottContinuous topElem)))))))

end DomainTheory.DataTypesAsLattices
