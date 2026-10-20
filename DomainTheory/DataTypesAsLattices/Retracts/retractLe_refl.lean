module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.IsRetract
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem retractLe_refl {a : Pomega} (ha : IsRetract a) : retractLe a a :=
  ⟨ha, ha⟩

end DomainTheory.DataTypesAsLattices
