module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmOp_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmOp_strBot_expand
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.iterElem_zerou27
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.iterElem_succ
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.iterate_expand_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.strBot_nil

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419


/-- **Exercise 5.16 (the approximants).** The `(k+1)`-st approximant of the least fixed point is the
partial element of the `k`-fold Thue–Morse morphism iterate of `[0]`:
`Φᵏ⁺¹(⊥) = (expandᵏ[0])⊥`. -/
theorem iterElem_succ_eq (k : ℕ) :
    tmOp.iterElem (k + 1) = strBot (expand^[k] [false]) := by
  induction k with
  | zero =>
    rw [iterElem_succ, iterElem_zero', ← strBot_nil, tmOp_strBot]
    rfl
  | succ k ih =>
    obtain ⟨ρ, hρ⟩ := iterate_expand_cons k
    rw [iterElem_succ, ih, hρ, tmOp_strBot_expand, ← hρ, Function.iterate_succ_apply']

end DomainTheory.NeighbourhoodSystems.Exercise516
