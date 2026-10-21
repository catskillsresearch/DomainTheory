/-ai
The language of a total tree is the set of words whose selected subtree has positive root label.

The root-label law for selected subtrees is applied, and the two sides then agree by reflexivity.
ai-/
module

public import Mathlib.Computability.MyhillNerode
import all Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Example62Regular

open Language

variable {n : ℕ}










/-- `L_a` is genuinely `{σ ∣ pos(aσ) = true}` as Scott writes it. -/
theorem treeLang_eq_pos (a : Tree n) : treeLang a = {σ | pos (select a σ) = true} := by
  simp only [pos_select]; rfl

end Example62Regular
end DomainTheory.NeighbourhoodSystems
