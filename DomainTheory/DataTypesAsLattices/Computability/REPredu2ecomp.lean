module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




theorem REPred.comp {α β} [Primcodable α] [Primcodable β] {p : β → Prop}
    (hp : REPred p) {f : α → β} (hf : Computable f) :
    REPred fun a => p (f a) :=
  Partrec.comp hp hf

end DomainTheory.DataTypesAsLattices
