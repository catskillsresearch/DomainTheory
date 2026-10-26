module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.ScottContinuousFin
public import DomainTheory.DataTypesAsLattices.Lambda.nestApplyFin
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.beta

@[expose] public section

namespace DomainTheory.DataTypesAsLattices
/-- Nested-graph representative of an n-ary continuous map. -/
def curryFin : ∀ {n : ℕ}, ((Fin n → Pomega) → Pomega) → Pomega
  | 0, f => f Fin.elim0
  | _n + 1, f => graph (fun x => curryFin (fun xs => f (Fin.cons x xs)))

namespace curryFin

theorem isScottContinuous {n : ℕ} :
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

theorem app {n : ℕ} {f : (Fin n → Pomega) → Pomega}
    (hf : ScottContinuousFin f) (xs : Fin n → Pomega) :
    nestApplyFin (curryFin f) xs = f xs := by
  induction n with
  | zero =>
    change curryFin f = f xs
    exact congrArg f (funext fun i => nomatch i)
  | succ n ih =>
    have hβ : funOf (curryFin f) (xs 0) =
        curryFin (fun ys => f (Fin.cons (xs 0) ys)) :=
      beta (curryFin.isScottContinuous hf) (xs 0)
    change nestApplyFin (funOf (curryFin f) (xs 0)) (Fin.tail xs) = f xs
    rw [hβ, ih ⟨hf.out.2 (xs 0)⟩ (Fin.tail xs)]
    exact congrArg f (Fin.cons_self_tail xs)

end curryFin

end DomainTheory.DataTypesAsLattices
