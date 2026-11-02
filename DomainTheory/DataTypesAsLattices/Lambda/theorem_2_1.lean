module

public import DomainTheory.DataTypesAsLattices.Lambda.interp
import Mathlib.Tactic.Bound.Init
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_2_1 (t : Term) (ρ : ℕ → Pomega) (i : ℕ) :
    IsScottContinuous (fun v => interp t (envSet ρ i v)) :=
  interp.var_isScottContinuous t ρ i

end DomainTheory.DataTypesAsLattices
