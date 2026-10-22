/-ai
If g is primitive recursive, then so is the function sending n to 2 raised to the power g n.

It is exponentiation composed with the pairing of the constant 2 and g, and the two sides agree after simplifying the unpaired projections.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_pow

@[expose] public section


namespace Domain.Recursive


/-- `n ↦ 2 ^ g n` is primitive recursive when `g` is. -/
theorem primrec_two_pow {g : ℕ → ℕ} (hg : Nat.Primrec g) : Nat.Primrec (fun n => 2 ^ g n) :=
  (primrec_pow.comp ((Nat.Primrec.const 2).pair hg)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]

end Domain.Recursive
