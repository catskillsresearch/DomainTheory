/-ai
Scott's function-space theorem for algebraic lattices says that the function-space retract of two closures is a retract.

The retract equation is equality with the graph of the double application. By graph extensionality it is enough to check each argument, and rewriting by idempotence of the function-space retract for the two underlying retracts, together with the application law for that retract, makes the two sides agree.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 5.3 (The function space theorem for algebraic
lattices).** The function-space retract of two closures is a retract. -/
theorem theorem_5_3 {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsRetract (arrowR a b) := by
  change arrowR a b = graph (fun x => funOf (arrowR a b) (funOf (arrowR a b) x))
  apply graph_ext
  intro u
  rw [theorem_4_3_i ha.2 hb.2, arrowR_app]

end DomainTheory.DataTypesAsLattices
