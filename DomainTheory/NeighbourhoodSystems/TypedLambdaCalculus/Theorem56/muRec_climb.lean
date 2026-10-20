module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muRec_step

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)












section Mu

variable (f : ApproximableMap (prod N N) N)





/-- The search advances over a run of positive totals: if `f((n+i)^, m̂)` is a positive total for
all `i < k`, then `ḡ(n̂, m̂) = ḡ((n+k)^, m̂)`. -/
theorem muRec_climb (m : ℕ) :
    ∀ (k n : ℕ), (∀ i < k, ∃ j, f.toElementMap (pair (natElem (n + i)) (natElem m)) = natElem (j + 1)) →
      (muRec f).toElementMap (pair (natElem n) (natElem m)) =
        (muRec f).toElementMap (pair (natElem (n + k)) (natElem m)) := by
  intro k
  induction k with
  | zero => intro n _; rw [Nat.add_zero]
  | succ k ih =>
    intro n h
    obtain ⟨j, hj⟩ := h 0 (Nat.succ_pos k)
    rw [Nat.add_zero] at hj
    have key := ih (n + 1) (fun i hi => by
      obtain ⟨j', hj'⟩ := h (i + 1) (by omega)
      exact ⟨j', by rw [show n + 1 + i = n + (i + 1) by omega]; exact hj'⟩)
    rw [muRec_step f hj, key, show n + 1 + k = n + (k + 1) by omega]

end Mu
end DomainTheory.NeighbourhoodSystems.Theorem56
