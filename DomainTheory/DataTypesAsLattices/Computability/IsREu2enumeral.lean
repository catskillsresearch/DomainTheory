/-ai
The singleton of a natural number is recursively enumerable.

Equality with that number is a computable predicate, because boolean equality of the identity with the constant value is primitive recursive, and that predicate agrees with membership in the singleton.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- Named `numeral` so it does not shadow `ofNat`. -/
theorem IsRE.numeral (k : ℕ) : IsRE (ofNat k) := by
  have : ComputablePred fun n : ℕ => n = k :=
    ⟨inferInstance, (Primrec.beq.comp Primrec.id (Primrec.const k)).to_comp⟩
  exact REPred.of_eq this.to_re fun n => by simp [ofNat]

end DomainTheory.DataTypesAsLattices
