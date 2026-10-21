/-ai
Scott 1976, Theorem 4.5 (iii). The sum preserves the retract ordering: if a ⊑ a' and b ⊑ b', then a ⊕ b ⊑ a' ⊕ b'.

Each identity required by the ordering of the sums is equation (4.13), reversed. Before that equation is applied, the composites of the factors are replaced by the corresponding identities from a ⊑ a' and from b ⊑ b'.
ai-/

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
