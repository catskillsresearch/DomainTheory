
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_12

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.4 (iv).** `⊗` is a functor on maps. -/
theorem tensorR_functor {a b a' b' f f' : Pomega}
    (_ha : Retract a) (_hb : Retract b)
    (_ha' : Retract a') (_hb' : Retract b')
    (hf : typed f (arrowR a b)) (hf' : typed f' (arrowR a' b')) :
    typed (tensorR f f') (arrowR (tensorR a a') (tensorR b b')) := by
  change tensorR f f' =
    funOf (arrowR (tensorR a a') (tensorR b b')) (tensorR f f')
  rw [arrowR_app]
  have h := eq_4_12 b b' f f'
  have h' := eq_4_12 f f' a a'
  have hf1 := typed_of_arrowR hf
  have hf2 := typed_of_arrowR hf'
  apply Eq.symm
  calc
    comp (tensorR b b') (comp (tensorR f f') (tensorR a a'))
        = comp (tensorR b b') (tensorR (comp f a) (comp f' a')) := by
          rw [eq_4_12]
    _ = tensorR (comp b (comp f a)) (comp b' (comp f' a')) := eq_4_12 _ _ _ _
    _ = tensorR f f' := by
      rw [← hf1, ← hf2]

end DomainTheory.DataTypesAsLattices
