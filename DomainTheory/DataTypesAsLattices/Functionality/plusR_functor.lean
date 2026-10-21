/-ai
Scott 1976, Theorem 4.5 (iv). The sum is a covariant functor: if f has type a → b and f' has type a' → b', then the sum of f and f' has type the arrow from the sum of a and a' to the sum of b and b'.

Unfolding function-space application turns the typing equation into a composite. The two arrow typings supply the composite equations for f and f'. Two uses of equation (4.13) move the sum inside those composites, and substituting the typing equations returns the sum of f and f'.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_13

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





















/-- **Scott 1976, Theorem 4.5 (iv).** `⊕` is a covariant functor. -/
theorem plusR_functor {a b a' b' f f' : Pomega}
    (_ha : IsRetract a) (_hb : IsRetract b)
    (_ha' : IsRetract a') (_hb' : IsRetract b')
    (hf : typed f (arrowR a b)) (hf' : typed f' (arrowR a' b')) :
    typed (plusR f f') (arrowR (plusR a a') (plusR b b')) := by
  change plusR f f' =
    funOf (arrowR (plusR a a') (plusR b b')) (plusR f f')
  rw [arrowR_app]
  have hf1 := typed_of_arrowR hf
  have hf2 := typed_of_arrowR hf'
  apply Eq.symm
  calc
    comp (plusR b b') (comp (plusR f f') (plusR a a'))
        = comp (plusR b b') (plusR (comp f a) (comp f' a')) := by
          rw [eq_4_13]
    _ = plusR (comp b (comp f a)) (comp b' (comp f' a')) := eq_4_13 _ _ _ _
    _ = plusR f f' := by
      rw [← hf1, ← hf2]

end DomainTheory.DataTypesAsLattices
