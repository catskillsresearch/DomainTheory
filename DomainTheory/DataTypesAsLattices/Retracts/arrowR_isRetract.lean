/-ai
If a and b are retracts, then the function space from a to b is a retract.

Graph extensionality reduces the retract equation to an equality of values. That equality is the first clause of Theorem 4.3, rewritten by the application law for the function-space retract.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_app
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_3_i

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









































theorem arrowR_isRetract {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (arrowR a b) := by
  change arrowR a b =
    graph (fun x => funOf (arrowR a b) (funOf (arrowR a b) x))
  apply graph_ext
  intro u
  rw [theorem_4_3_i ha hb, arrowR_app]

end DomainTheory.DataTypesAsLattices
