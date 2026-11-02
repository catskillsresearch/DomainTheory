module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_2
public import DomainTheory.DataTypesAsLattices.Lambda.condSet

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def primRecStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2 (.lam 3
    (.cond (.var 3) (.var 0)
      (.app (.app (.var 1) (.pred (.var 3)))
        (.app (.var 2) (.pred (.var 3))))))))

namespace primRecStepTerm

theorem interp (a f u n : Pomega) :
    funOf (funOf (funOf (funOf (interp primRecStepTerm (fun _ => botElem)) a) f) u) n =
      condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))) := by
  change funOf (funOf (funOf (funOf (DomainTheory.DataTypesAsLattices.interp (Term.lam 0 _) (fun _ => botElem)) a) f) u) n = _
  rw [theorem_2_2.beta]
  rw [theorem_2_2.beta]
  rw [theorem_2_2.beta]
  rw [theorem_2_2.beta]
  simp [_root_.DomainTheory.DataTypesAsLattices.interp, envSet, Function.update]

end primRecStepTerm

end DomainTheory.DataTypesAsLattices
