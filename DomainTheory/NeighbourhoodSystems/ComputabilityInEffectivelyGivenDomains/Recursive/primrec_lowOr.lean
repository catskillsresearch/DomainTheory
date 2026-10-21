/-ai
The function of a pair code that returns the low-bit disjunction of its two components is primitive recursive.

The remainders modulo 2 of the two components are primitive recursive. One minus one minus their sum agrees with the low-bit disjunction by definition.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_mod2

@[expose] public section


namespace Domain.Recursive


theorem primrec_lowOr : Nat.Primrec (fun t => lowOr t.unpair.1 t.unpair.2) := by
  have hx : Nat.Primrec (fun t : ℕ => t.unpair.1 % 2) := primrec_mod2.comp Nat.Primrec.left
  have hy : Nat.Primrec (fun t : ℕ => t.unpair.2 % 2) := primrec_mod2.comp Nat.Primrec.right
  exact (primrec_sub₂ (Nat.Primrec.const 1)
    (primrec_sub₂ (Nat.Primrec.const 1) (primrec_add₂ hx hy))).of_eq fun _ => rfl

end Domain.Recursive
