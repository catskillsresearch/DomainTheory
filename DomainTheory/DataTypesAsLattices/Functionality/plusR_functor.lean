
module

public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_13
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.5 (iv).** `⊕` is a covariant functor. -/
theorem plusR_functor {a b a' b' f f' : Pomega}
    (_ha : Retract a) (_hb : Retract b)
    (_ha' : Retract a') (_hb' : Retract b')
    (hf : typed f (arrowR a b)) (hf' : typed f' (arrowR a' b')) :
    typed (plusR f f') (arrowR (plusR a a') (plusR b b')) := by
  change plusR f f' =
    funOf (arrowR (plusR a a') (plusR b b')) (plusR f f')
  rw [arrowR.app]
  have hf1 := arrowR.typed_of hf
  have hf2 := arrowR.typed_of hf'
  apply Eq.symm
  calc
    comp (plusR b b') (comp (plusR f f') (plusR a a'))
        = comp (plusR b b') (plusR (comp f a) (comp f' a')) := by
          rw [eq_4_13]
    _ = plusR (comp b (comp f a)) (comp b' (comp f' a')) := eq_4_13 _ _ _ _
    _ = plusR f f' := by
      rw [← hf1, ← hf2]

end DomainTheory.DataTypesAsLattices
