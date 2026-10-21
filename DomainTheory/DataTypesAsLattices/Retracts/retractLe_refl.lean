/-ai
The retract order is reflexive on retracts.

Both composites of a retract with itself equal the retract, by the retract equation.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.IsRetract
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem retractLe_refl {a : Pomega} (ha : IsRetract a) : retractLe a a :=
  ⟨ha, ha⟩

end DomainTheory.DataTypesAsLattices
