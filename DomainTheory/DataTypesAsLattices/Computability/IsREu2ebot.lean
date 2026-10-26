module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eempty

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem IsRE.bot : IsRE botElem :=
  ⟨REPred.empty.of_eq fun n => by simp [botElem]⟩

end DomainTheory.DataTypesAsLattices
