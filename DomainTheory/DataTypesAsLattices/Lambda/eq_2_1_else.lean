module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.maxExtend
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem eq_2_1_else (p : ℕ → Pomega) {x : Pomega}
    (hne : x ≠ botElem) (hsing : ∀ n, x ≠ ofNat n) :
    maxExtend p x = topElem := by
  ext k
  constructor
  · intro; trivial
  · intro
    exact Or.inr (Or.inr ⟨hne, hsing⟩)

end DomainTheory.DataTypesAsLattices
