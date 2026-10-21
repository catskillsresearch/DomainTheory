/-ai
The sink state of the single-word automaton stays the sink after every word.

The proof is by induction on the word. The empty word leaves the state unchanged. A longer word rewrites by the cons equation for evaluation and applies the inductive hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.DFA
import all Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Option
import all Mathlib.Data.Fintype.Option
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability


/-- The dead state `none` is a sink. -/
theorem singleDFA_evalFrom_none (σ : List Bool) (w : List Bool) :
    (singleDFA σ).evalFrom none w = none := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [DFA.evalFrom_cons]; exact ih

end Exercise722
end DomainTheory.NeighbourhoodSystems
