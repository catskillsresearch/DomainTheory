/-ai
The Cantor pairing function is primitive recursive in its two arguments.

Pairing is recovered as the sum of the second argument with the quotient by 2 of the product of the sum of the arguments and one more than that sum, using addition, multiplication, division, and successor, and this expression is identified with pair by reflexivity.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp

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
