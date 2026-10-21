/-ai
The doubly strict conditional on the numeral n + 1 returns its right argument.

That numeral omits 0 and contains the positive number n, so the positive-and-not-zero case applies.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_of_pos_not_zero

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem dcondSet_ofNat_succ (n : ℕ) (x y : Pomega) :
    dcondSet (ofNat (n + 1)) x y = y :=
  dcondSet_of_pos_not_zero (by simp [ofNat]) ⟨n, by simp [ofNat]⟩

end DomainTheory.DataTypesAsLattices
