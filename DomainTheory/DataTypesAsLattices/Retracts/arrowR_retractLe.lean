module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.eq_4_11_comp

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem arrowR_retractLe {a b a' b' : Pomega}
    (hab : retractLe a a') (hbb : retractLe b b') :
    retractLe (arrowR a b) (arrowR a' b') := by
  constructor
  · have h : arrowR (comp a' a) (comp b b') = arrowR a b := by
      rw [← hab.2, ← hbb.1]
    exact (h.symm.trans (eq_4_11_comp a b a' b').symm)
  · have h : arrowR (comp a a') (comp b' b) = arrowR a b := by
      rw [← hab.1, ← hbb.2]
    exact (h.symm.trans (eq_4_11_comp a' b' a b).symm)

end DomainTheory.DataTypesAsLattices
