module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.zeroC
public import DomainTheory.DataTypesAsLattices.Lambda.sucC
public import DomainTheory.DataTypesAsLattices.Lambda.predC
public import DomainTheory.DataTypesAsLattices.Lambda.condC
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2efunOf
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2eScomb
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2eKcomb
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2econdC
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2epredC
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2esucC
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2ezeroC
public import DomainTheory.DataTypesAsLattices.Computability.pack4

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



/-- Combinatory elements are r.e. (one direction of the appendix equivalence). -/
theorem combinatory_isRE {u : Pomega} (hu : IsCombinatory u) : IsRE u := by
  induction hu with
  | zero => exact IsRE.zeroC
  | suc => exact IsRE.sucC
  | pred => exact IsRE.predC
  | cond => exact IsRE.condC
  | K => exact IsRE.Kcomb
  | S => exact IsRE.Scomb
  | app _ _ iu iv => exact IsRE.funOf iu iv

end DomainTheory.DataTypesAsLattices
