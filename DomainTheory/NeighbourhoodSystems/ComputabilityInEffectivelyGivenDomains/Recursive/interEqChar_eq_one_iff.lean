module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.Basic

@[expose] public section


namespace Domain.Recursive


open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722


theorem interEqChar_eq_one_iff {fuel : ℕ} {e1 e2 : SExpr}
    (h1 : c9b5_sexprDepth e1 ≤ fuel) (h2 : c9b5_sexprDepth e2 ≤ fuel) :
    interEqChar fuel (c9b5_sexprGodelEncode e1) (c9b5_sexprGodelEncode e2) = 1 ↔
      denote e1 = denote e2 := by
  unfold interEqChar
  rw [mulBit_eq_one_iff, subsetBChar_eq_one_iff h1 h2, subsetBChar_eq_one_iff h2 h1,
    ← Set.Subset.antisymm_iff]

end Domain.Recursive
