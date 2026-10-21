/-ai
If b is strict, then the function space from a to b is strict.

The application law writes the value at the empty set as b composed after the empty set composed after a. The inner composition unfolds to the graph of a constant empty map, which equals the empty set. The outer composition is then the graph of the constant value of b at the empty set, and strictness of b together with the constant-empty graph makes that value the empty set.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









































theorem arrowR_isStrict {a b : Pomega} (hb : IsStrict b) :
    IsStrict (arrowR a b) := by
  change funOf (arrowR a b) botElem = botElem
  rw [arrowR_app]
  have hbot : comp botElem a = botElem := by
    unfold comp
    simp [funOf_botElem, graph_const_bot]
  rw [hbot]
  unfold comp
  simp only [funOf_botElem]
  exact (congrArg graph (funext fun _ => hb)).trans graph_const_bot

end DomainTheory.DataTypesAsLattices
