/-ai
Interpreting the primitive-recursion step term in the constantly bottom environment and applying the result to a base, a step, a functional, and an argument yields the conditional that returns the base on zero and otherwise applies the step and then the functional to the predecessor.

Four uses of the beta clause of Theorem 2.2 are followed by simplification of interpretation and environment update.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_2_beta

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem primRecStepTerm_interp (a f u n : Pomega) :
    funOf (funOf (funOf (funOf (interp primRecStepTerm (fun _ => botElem)) a) f) u) n =
      condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))) := by
  change funOf (funOf (funOf (funOf (interp (.lam 0 _) (fun _ => botElem)) a) f) u) n = _
  rw [theorem_2_2_beta]
  rw [theorem_2_2_beta]
  rw [theorem_2_2_beta]
  rw [theorem_2_2_beta]
  simp [interp, envSet, Function.update]

end DomainTheory.DataTypesAsLattices
