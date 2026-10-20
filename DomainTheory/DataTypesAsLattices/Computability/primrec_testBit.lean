module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.primrec_twoPow

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




theorem primrec_testBit : Primrec₂ fun n k : ℕ => n.testBit k :=
  (Primrec.eq.decide.comp
    (Primrec.nat_mod.comp
      (Primrec.nat_div.comp Primrec.fst (primrec_twoPow.comp Primrec.snd))
      (Primrec.const 2))
    (Primrec.const 1)).of_eq fun _p =>
      Nat.testBit_eq_decide_div_mod_eq.symm

end DomainTheory.DataTypesAsLattices
