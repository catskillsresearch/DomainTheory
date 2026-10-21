/-ai
The integer functional is Scott continuous.

Continuity of graph formation reduces the claim to continuity in the functional argument. Theorem 1.3 substitutes the outer conditional, continuous in its third argument, into the inner conditional. A second use of Theorem 1.3 substitutes that inner conditional, continuous in its first argument, into application in the function argument at the predecessor.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices













































theorem intF_isScottContinuous : IsScottContinuous intF :=
  graph_const_isScottContinuous
    (fun f u => dcondSet u (ofNat 0) (dcondSet (funOf f (predSet u)) u u))
    (fun u =>
      theorem_1_3
        (f := fun z => dcondSet u (ofNat 0) z)
        (g := fun f => dcondSet (funOf f (predSet u)) u u)
        (dcondSet_isScottContinuous_right u (ofNat 0))
        (theorem_1_3
          (f := fun z => dcondSet z u u)
          (g := fun f => funOf f (predSet u))
          (dcondSet_isScottContinuous_left u u)
          (funOf_isScottContinuous_left (predSet u))))

end DomainTheory.DataTypesAsLattices
