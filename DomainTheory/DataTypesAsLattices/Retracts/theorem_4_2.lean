module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















/-- **Scott 1976, Theorem 4.2 (The partial ordering theorem).** -/
theorem theorem_4_2 {a b c : Pomega} :
    (IsRetract a → retractLe a a) ∧
      (retractLe a b → retractLe b a → a = b) ∧
      (retractLe a b → retractLe b c → retractLe a c) := by
  refine ⟨retractLe_refl, ?_, ?_⟩
  · intro hab hba
    exact hab.1.trans (hba.2.symm)
  · intro hab hbc
    exact retractLe_trans hab hbc

end DomainTheory.DataTypesAsLattices
