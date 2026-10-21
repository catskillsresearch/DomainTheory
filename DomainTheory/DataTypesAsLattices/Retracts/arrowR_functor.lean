/-ai
If f has type the function space from a to b and f' has type the function space from a' to b', then the function space from f to f' has type the function space from the function space of b and a' to the function space of a and b'.

Typing is the equality of the function space of f and f' with the application of the outer function space to it. The application law rewrites that application as a composition of function spaces. The composition law for function spaces is used on the inner pair and again on the outer pair. The two typing hypotheses, applied at an argument and simplified by the law of composition, say that f absorbs a and b and that f' absorbs a' and b'. Two graph extensionalities then match the resulting applications, rewriting with the identity for f and reversing the identity for f'.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_app
public import DomainTheory.DataTypesAsLattices.Retracts.typed_of_arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.eq_4_11_comp

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









































theorem arrowR_functor {a b a' b' f f' : Pomega}
    (hf : typed f (arrowR a b)) (hf' : typed f' (arrowR a' b')) :
    typed (arrowR f f') (arrowR (arrowR b a') (arrowR a b')) := by
  change arrowR f f' =
    funOf (arrowR (arrowR b a') (arrowR a b')) (arrowR f f')
  rw [arrowR_app]
  have inner := eq_4_11_comp f f' b a'
  have outer := eq_4_11_comp a b' (comp b f) (comp f' a')
  have hf1 := typed_of_arrowR hf
  have hf2 := typed_of_arrowR hf'
  apply Eq.symm
  calc
    comp (arrowR a b') (comp (arrowR f f') (arrowR b a'))
        = comp (arrowR a b') (arrowR (comp b f) (comp f' a')) := by rw [inner]
    _ = arrowR (comp (comp b f) a) (comp b' (comp f' a')) := outer
    _ = arrowR f f' := by
      apply graph_ext
      intro u
      apply graph_ext
      intro x
      have hfx : funOf f x = funOf b (funOf f (funOf a x)) := by
        simpa [comp_app] using congrArg (fun w => funOf w x) hf1
      have hf'y : ∀ y, funOf f' y = funOf b' (funOf f' (funOf a' y)) := by
        intro y
        simpa [comp_app] using congrArg (fun w => funOf w y) hf2
      simp only [comp_app]
      rw [hfx]
      exact (hf'y _).symm

end DomainTheory.DataTypesAsLattices
