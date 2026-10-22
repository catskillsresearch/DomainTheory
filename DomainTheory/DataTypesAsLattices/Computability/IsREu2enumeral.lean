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
  constructor
  exact REPred.of_eq this.to_re fun n => by simp [ofNat]

end DomainTheory.DataTypesAsLattices
