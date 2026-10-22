module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem curryFin_isScottContinuous {n : ℕ} :
    ∀ {f : (Fin (n + 1) → Pomega) → Pomega},
      ScottContinuousFin f →
      IsScottContinuous (fun x => curryFin (fun xs : Fin n → Pomega => f (Fin.cons x xs))) := by
  induction n with
  | zero =>
    intro f hf
    exact hf.out.1 Fin.elim0
  | succ n ih =>
    intro f hf
    refine graph_const_isScottContinuous
      (fun x y => curryFin (fun zs : Fin n → Pomega =>
        f (Fin.cons x (Fin.cons y zs)))) (fun y =>
      ih (f := fun xs : Fin (n + 1) → Pomega =>
          f (Fin.cons (xs 0) (Fin.cons y (Fin.tail xs)))) ⟨⟨?_, ?_⟩⟩)
    · intro zs
      simpa [Fin.cons_zero, Fin.cons_succ] using hf.out.1 (Fin.cons y zs)
    · intro x
      simpa [Fin.cons_zero, Fin.cons_succ] using (hf.out.2 x).2 y

end DomainTheory.DataTypesAsLattices
