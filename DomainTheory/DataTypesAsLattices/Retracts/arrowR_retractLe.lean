/-ai
If a lies below a' and b lies below b' in the retract order, then the function space from a to b lies below the function space from a' to b'.

Each projection equation is the composition law for function spaces. One side rewrites the composed retracts by the equations a = a' ∘ a and b = b ∘ b'. The other side rewrites them by a = a ∘ a' and b = b' ∘ b.
ai-/
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
