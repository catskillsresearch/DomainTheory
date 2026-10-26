module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Retracts.comp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem IsRE.predSet {x : Pomega} (hx : IsRE x) : IsRE (predSet x) :=
  ⟨REPred.of_eq (hx.out.comp Primrec.succ.to_comp) fun _ => Iff.rfl⟩

end DomainTheory.DataTypesAsLattices
