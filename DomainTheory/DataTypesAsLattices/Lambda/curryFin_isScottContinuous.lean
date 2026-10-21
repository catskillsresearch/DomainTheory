/-ai
Currying one argument of a finitely Scott-continuous map yields a Scott-continuous map into nested graphs.

When one argument remains, this is the given continuity in that coordinate. When more remain, the result is the graph of a map continuous in the next argument. The induction hypothesis supplies that continuity after the two cons operations are reassociated, using continuity of the original map in each coordinate.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



















theorem curryFin_isScottContinuous {n : ℕ} :
    ∀ {f : (Fin (n + 1) → Pomega) → Pomega},
      IsScottContinuousFin f →
      IsScottContinuous (fun x => curryFin (fun xs : Fin n → Pomega => f (Fin.cons x xs))) := by
  induction n with
  | zero =>
    intro f hf
    exact hf.1 Fin.elim0
  | succ n ih =>
    intro f hf
    refine graph_const_isScottContinuous
      (fun x y => curryFin (fun zs : Fin n → Pomega =>
        f (Fin.cons x (Fin.cons y zs)))) (fun y =>
      ih (f := fun xs : Fin (n + 1) → Pomega =>
          f (Fin.cons (xs 0) (Fin.cons y (Fin.tail xs)))) ⟨?_, ?_⟩)
    · intro zs
      simpa [Fin.cons_zero, Fin.cons_succ] using hf.1 (Fin.cons y zs)
    · intro x
      simpa [Fin.cons_zero, Fin.cons_succ] using (hf.2 x).2 y

end DomainTheory.DataTypesAsLattices
