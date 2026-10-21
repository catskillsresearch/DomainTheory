/-ai
Scott 1976, Theorem 4.4 (iv). The product acts as a functor on maps: if f lies in the function space from a to b and f' lies in the function space from a' to b', then f ⊗ f' lies in the function space from a ⊗ a' to b ⊗ b'.

Unfold the function-space equation by the application law for the arrow. Equation (4.12) slides the product inside composition twice, first past the composite with a ⊗ a' and then past the composite with b ⊗ b'. The typing equations replace b ∘ f ∘ a by f and b' ∘ f' ∘ a' by f'.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_12

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, Theorem 4.4 (iv).** `⊗` is a functor on maps. -/
theorem tensorR_functor {a b a' b' f f' : Pomega}
    (_ha : IsRetract a) (_hb : IsRetract b)
    (_ha' : IsRetract a') (_hb' : IsRetract b')
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
