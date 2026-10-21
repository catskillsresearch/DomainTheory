/-ai
A continuous map of finitely many arguments is computable when it is continuous in those arguments and its nested graph, the pairing encoding of membership in the value on finite arguments, is recursively enumerable.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.IsRE

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- **Scott 1976, §2, Definition.** A `k`-ary continuous map is computable
when its nested graph (the pairing encoding of
`m ∈ f(e n₀)⋯(e n_{k-1})`) is r.e. -/
def IsComputableFin {n : ℕ} (f : (Fin n → Pomega) → Pomega) : Prop :=
  IsScottContinuousFin f ∧ IsRE (curryFin f)

end DomainTheory.DataTypesAsLattices
