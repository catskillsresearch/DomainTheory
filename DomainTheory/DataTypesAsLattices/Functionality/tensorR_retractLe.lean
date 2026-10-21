/-ai
Scott 1976, Theorem 4.4 (iii). The product preserves the retract ordering: if a ⊑ a' and b ⊑ b', then a ⊗ b ⊑ a' ⊗ b'.

Each identity required by the ordering of the products is equation (4.12), reversed. Before that equation is applied, the composites of the factors are replaced by the corresponding identities from a ⊑ a' and from b ⊑ b'.
ai-/

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
