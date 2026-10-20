module

public import Mathlib.Data.Nat.Sqrt
import all Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
import all Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
import all Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
import all Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_pair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_pair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn_ite
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.isOne_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.isOne_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.natEqChar_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.c9b5_encodeListBool

@[expose] public section

set_option linter.unusedSectionVars false

namespace Domain.Recursive

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

/-- Gödel code mirroring `SExpr.encode` in `Exercise722Presentation.lean`. -/
def c9b5_sexprGodelEncode : SExpr → ℕ
  | .sigma => Nat.pair 0 0
  | .single σ => Nat.pair 1 (c9b5_encodeListBool σ)
  | .cat a b => Nat.pair 2 (Nat.pair (c9b5_sexprGodelEncode a) (c9b5_sexprGodelEncode b))
  | .cap a b => Nat.pair 3 (Nat.pair (c9b5_sexprGodelEncode a) (c9b5_sexprGodelEncode b))

end Domain.Recursive
