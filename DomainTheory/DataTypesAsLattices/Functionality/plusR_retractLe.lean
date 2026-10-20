module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_13

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





















/-- **Scott 1976, Theorem 4.5 (iii).** `⊕` preserves `⊑`. -/
theorem plusR_retractLe {a b a' b' : Pomega}
    (hab : retractLe a a') (hbb : retractLe b b') :
    retractLe (plusR a b) (plusR a' b') := by
  constructor
  · have h : plusR (comp a a') (comp b b') = plusR a b := by
      rw [← hab.1, ← hbb.1]
    exact ((eq_4_13 a b a' b').trans h).symm
  · have h : plusR (comp a' a) (comp b' b) = plusR a b := by
      rw [← hab.2, ← hbb.2]
    exact ((eq_4_13 a' b' a b).trans h).symm

end DomainTheory.DataTypesAsLattices
