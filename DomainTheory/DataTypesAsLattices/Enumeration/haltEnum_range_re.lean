/-ai
The predicate of numbers that lie in the range of the shifted halting enumerator is recursively enumerable.

Membership is existence of a preimage under the enumerator. Equality of the enumerator on the second component with the first component is primitive recursive, hence a computable predicate and therefore recursively enumerable, and existential quantification preserves recursive enumerability.
ai-/
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















theorem haltEnum_range_re : REPred fun m => ∃ t, haltEnum t = m :=
  REPred.exists (p := fun m t => haltEnum t = m)
    ((Primrec.eq.comp (primrec_haltEnum.comp Primrec.snd) Primrec.fst).computablePred.to_re)

end DomainTheory.DataTypesAsLattices
