/-ai
If a predicate of an element of a primitive-codable inhabited type and a natural number is recursively enumerable as a predicate of pairs, then the predicate asserting that some natural number satisfies it is recursively enumerable.

Transport the predicate along decoding of the first component, using the default inhabitant where decoding fails, by the computable operations of pairing, decoding, projection, and the constant default. Existential quantification over the second component preserves recursive enumerability. Reindex that existential predicate along the computable encoding, and the encode-decode identity identifies the result with existence for the original element.
ai-/
module

public import Mathlib.Computability.Halting
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
