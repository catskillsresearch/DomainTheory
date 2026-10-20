module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_2_beta

@[expose] public section


namespace DomainTheory.DataTypesAsLattices























































theorem primRecStep_graph_of (a f : Pomega) :
    graph (primRecStep a f) =
      funOf (funOf (interp primRecStepTerm (fun _ => botElem)) a) f := by
  change graph (primRecStep a f) =
    funOf (funOf (interp (.lam 0 (.lam 1 (.lam 2 (.lam 3
      (.cond (.var 3) (.var 0)
        (.app (.app (.var 1) (.pred (.var 3)))
          (.app (.var 2) (.pred (.var 3))))))))) (fun _ => botElem)) a) f
  rw [theorem_2_2_beta, theorem_2_2_beta]
  apply congrArg graph
  funext u
  apply congrArg graph
  funext n
  simp [interp, envSet, Function.update]

end DomainTheory.DataTypesAsLattices
