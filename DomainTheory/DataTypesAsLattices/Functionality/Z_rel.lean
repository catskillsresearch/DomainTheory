/-ai
If a restricted equivalence is preserved by a pair of maps, and it relates two values, then it relates the iterates of those maps at those values.

Induct on the stage. Stage zero is the given relation. A successor applies the preservation hypothesis to the inductive relation.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices























theorem Z_rel (A : RestrictedEquiv) (n : ℕ) {f f' x y : Pomega}
    (hf : ∀ a b, A.rel a b → A.rel (funOf f a) (funOf f' b))
    (hxy : A.rel x y) :
    A.rel (Z n f x) (Z n f' y) := by
  induction n with
  | zero => simpa [Z] using hxy
  | succ n ih =>
    simpa [Z] using hf _ _ ih

end DomainTheory.DataTypesAsLattices
