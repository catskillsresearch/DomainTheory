/-ai
The predicate of numbers that lie in the range of the shifted halting enumerator is not computable.

Assume a decision procedure for membership in the range. Composing it with the successor makes membership of n + 1 computable, and the successor law for the enumerator converts that into computability of the domain of evaluation, on input 0, of the code decoded from n. Composing that decision procedure with encoding, and transporting by the identity between a code and the decoding of its encoding, makes the domain of evaluation of an arbitrary code on input 0 a computable predicate. That is the halting problem at input 0.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.haltEnum_succ_iff

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code















theorem haltEnum_range_not_computable :
    ¬ComputablePred fun m => ∃ t, haltEnum t = m := by
  intro hc
  have := hc.choose
  have hsucc : ComputablePred fun n : ℕ => ∃ t, haltEnum t = n + 1 :=
    Computable.computablePred
      ((ComputablePred.decide hc).comp Primrec.succ.to_comp)
  have hn : ComputablePred fun n : ℕ =>
      (eval (Denumerable.ofNat Code n) 0).Dom :=
    hsucc.of_eq fun n => haltEnum_succ_iff n
  have := hn.choose
  have : DecidablePred fun c : Code => (eval c 0).Dom :=
    fun c => decidable_of_iff
      (eval (Denumerable.ofNat Code (encode c)) 0).Dom
      (by simp [Denumerable.ofNat_encode])
  exact ComputablePred.halting_problem (n := 0)
    (Computable.computablePred
      ((ComputablePred.decide hn).comp Computable.encode |>.of_eq fun c => by
        simp [Denumerable.ofNat_encode]))

end DomainTheory.DataTypesAsLattices
