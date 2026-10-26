module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.ScottContinuousFin
public import DomainTheory.DataTypesAsLattices.Lambda.curryFin
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Graph.graph

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- **Scott 1976, §2, Definition.** A `k`-ary continuous map is computable
when its nested graph (the pairing encoding of
`m ∈ f(e n₀)⋯(e n_{k-1})`) is r.e. -/
class ComputableFin {n : ℕ} (f : (Fin n → Pomega) → Pomega) : Prop where
  out : ScottContinuousFin f ∧ IsRE (curryFin f)

end DomainTheory.DataTypesAsLattices
