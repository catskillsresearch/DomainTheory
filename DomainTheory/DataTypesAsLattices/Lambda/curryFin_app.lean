module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.curryFin_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem curryFin_app {n : ℕ} {f : (Fin n → Pomega) → Pomega}
    (hf : ScottContinuousFin f) (xs : Fin n → Pomega) :
    nestApplyFin (curryFin f) xs = f xs := by
  induction n with
  | zero =>
    change curryFin f = f xs
    exact congrArg f (funext fun i => nomatch i)
  | succ n ih =>
    have hβ : funOf (curryFin f) (xs 0) =
        curryFin (fun ys => f (Fin.cons (xs 0) ys)) :=
      beta (curryFin_isScottContinuous hf) (xs 0)
    change nestApplyFin (funOf (curryFin f) (xs 0)) (Fin.tail xs) = f xs
    rw [hβ, ih ⟨hf.out.2 (xs 0)⟩ (Fin.tail xs)]
    exact congrArg f (Fin.cons_self_tail xs)

end DomainTheory.DataTypesAsLattices
