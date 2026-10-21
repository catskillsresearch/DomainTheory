/-ai
For a fixed interpreter and environment, the interpreter step is Scott continuous in the expression.

The argument is a nest of ternary continuity for the definite conditional. The outermost test is application at the numeral zero, and the variable clause is continuous in the expression. The later tests are the iterated predecessors of the expression tag. The zero clause is constant, the successor through abstraction clauses are continuous in the expression, and the final alternative is the constant top element.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.hVar_isScottContinuous_e
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_expTag_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.hSucc_isScottContinuous_e
public import DomainTheory.DataTypesAsLattices.Functionality.hPred_isScottContinuous_e
public import DomainTheory.DataTypesAsLattices.Functionality.hCond_isScottContinuous_e
public import DomainTheory.DataTypesAsLattices.Functionality.hApp_isScottContinuous_e
public import DomainTheory.DataTypesAsLattices.Functionality.hLam_isScottContinuous_e

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Hstep_isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => Hstep H e t) :=
  continuous_nary
    (fun y z => dcondSet_isScottContinuous_left y z)
    (fun x z => dcondSet_isScottContinuous_mid x z)
    (fun x y => dcondSet_isScottContinuous_right x y)
    (funOf_isScottContinuous_left (ofNat 0))
    (hVar_isScottContinuous_e t)
    (continuous_nary
      (fun y z => dcondSet_isScottContinuous_left y z)
      (fun x z => dcondSet_isScottContinuous_mid x z)
      (fun x y => dcondSet_isScottContinuous_right x y)
      (predSet_iterate_expTag_isScottContinuous 1)
      (const_isScottContinuous hZero)
      (continuous_nary
        (fun y z => dcondSet_isScottContinuous_left y z)
        (fun x z => dcondSet_isScottContinuous_mid x z)
        (fun x y => dcondSet_isScottContinuous_right x y)
        (predSet_iterate_expTag_isScottContinuous 2)
        (hSucc_isScottContinuous_e H t)
        (continuous_nary
          (fun y z => dcondSet_isScottContinuous_left y z)
          (fun x z => dcondSet_isScottContinuous_mid x z)
          (fun x y => dcondSet_isScottContinuous_right x y)
          (predSet_iterate_expTag_isScottContinuous 3)
          (hPred_isScottContinuous_e H t)
          (continuous_nary
            (fun y z => dcondSet_isScottContinuous_left y z)
            (fun x z => dcondSet_isScottContinuous_mid x z)
            (fun x y => dcondSet_isScottContinuous_right x y)
            (predSet_iterate_expTag_isScottContinuous 4)
            (hCond_isScottContinuous_e H t)
            (continuous_nary
              (fun y z => dcondSet_isScottContinuous_left y z)
              (fun x z => dcondSet_isScottContinuous_mid x z)
              (fun x y => dcondSet_isScottContinuous_right x y)
              (predSet_iterate_expTag_isScottContinuous 5)
              (hApp_isScottContinuous_e H t)
              (continuous_nary
                (fun y z => dcondSet_isScottContinuous_left y z)
                (fun x z => dcondSet_isScottContinuous_mid x z)
                (fun x y => dcondSet_isScottContinuous_right x y)
                (predSet_iterate_expTag_isScottContinuous 6)
                (hLam_isScottContinuous_e H t)
                (const_isScottContinuous topElem)))))))

end DomainTheory.DataTypesAsLattices
