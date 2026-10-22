module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem IsRE.union {u v : Pomega} (hu : IsRE u) (hv : IsRE v) : IsRE (u ∪ v) :=
  ⟨REPred.of_eq (REPred.or hu.out hv.out) fun _ => Iff.rfl⟩

end DomainTheory.DataTypesAsLattices
