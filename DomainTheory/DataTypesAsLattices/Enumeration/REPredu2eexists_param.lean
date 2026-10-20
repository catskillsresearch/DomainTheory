module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code











theorem REPred.exists_param {α} [Primcodable α] [Inhabited α] {p : α → ℕ → Prop}
    (hp : REPred fun q : α × ℕ => p q.1 q.2) :
    REPred fun a => ∃ n, p a n := by
  have hN : REPred fun q : ℕ × ℕ => p ((decode q.1).getD default) q.2 :=
    hp.comp (Computable.pair
      (Computable.option_getD (Computable.decode.comp Computable.fst)
        (Computable.const default))
      Computable.snd)
  have hex : REPred fun n : ℕ => ∃ m, p ((decode n).getD default) m :=
    REPred.exists (p := fun n m => p ((decode n).getD default) m) hN
  exact _root_.REPred.of_eq (hex.comp Computable.encode) fun a => by
    simp [encodek]

end DomainTheory.DataTypesAsLattices
