module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem retractLe_refl {a : Pomega} (ha : Retract a) : retractLe a a :=
  ⟨ha.out, ha.out⟩

end DomainTheory.DataTypesAsLattices
