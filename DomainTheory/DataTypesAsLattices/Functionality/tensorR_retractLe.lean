module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_12

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, Theorem 4.4 (iii).** `⊗` preserves `⊑`. -/
theorem tensorR_retractLe {a b a' b' : Pomega}
    (hab : retractLe a a') (hbb : retractLe b b') :
    retractLe (tensorR a b) (tensorR a' b') := by
  constructor
  · have h : tensorR (comp a a') (comp b b') = tensorR a b := by
      rw [← hab.1, ← hbb.1]
    exact ((eq_4_12 a b a' b').trans h).symm
  · have h : tensorR (comp a' a) (comp b' b) = tensorR a b := by
      rw [← hab.2, ← hbb.2]
    exact ((eq_4_12 a' b' a b).trans h).symm

end DomainTheory.DataTypesAsLattices
