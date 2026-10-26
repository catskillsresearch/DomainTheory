module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2etrue

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem IsRE.top : IsRE topElem :=
  ⟨REPred.true.of_eq fun n => by simp [topElem]⟩

end DomainTheory.DataTypesAsLattices
