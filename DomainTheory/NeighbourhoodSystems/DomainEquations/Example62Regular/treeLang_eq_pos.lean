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
