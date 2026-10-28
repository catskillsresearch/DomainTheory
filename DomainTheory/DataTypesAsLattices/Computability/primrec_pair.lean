module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Retracts.comp

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem primrec_pair : Primrec₂ pair :=
  (Primrec.nat_add.comp
    (Primrec.nat_div.comp
      (Primrec.nat_mul.comp
        (Primrec.nat_add.comp Primrec.fst Primrec.snd)
        (Primrec.succ.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd)))
      (Primrec.const 2))
    Primrec.snd).of_eq fun _ => rfl

end DomainTheory.DataTypesAsLattices
