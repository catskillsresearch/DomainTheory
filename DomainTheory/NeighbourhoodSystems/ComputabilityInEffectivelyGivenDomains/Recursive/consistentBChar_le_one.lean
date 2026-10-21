/-ai
The consistency character of any fuel and any two codes is at most 1.

The bound is the corresponding bound for the nonemptiness character.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.decideNonemptyBChar_le_one

@[expose] public section


namespace Domain.Recursive


open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722


/-- Fuel is sized for the *outer* `.cap a b` expression (matching the convention of
`decideNonemptyBChar_eq_one_iff` / `matchesBChar_eq_one_iff`), one more than either child alone
needs, since `c9b5_sexprDepth (.cap a b) = 1 + max (c9b5_sexprDepth a) (c9b5_sexprDepth b)`. -/
theorem consistentBChar_le_one (fuel c1 c2 : ℕ) : consistentBChar fuel c1 c2 ≤ 1 :=
  decideNonemptyBChar_le_one _ _

end Domain.Recursive
