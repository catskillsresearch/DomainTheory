/-ai
The half-parity of a natural equals the pair of its quotient by 2 and its residue modulo 2.

The proof is by induction on the natural. The case 0 is definitional. At a successor, rewrite the recursive formula by the inductive hypothesis and the two unpairing equations; the two components then agree by arithmetic.
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

@[expose] public section


namespace Domain.Recursive


theorem halfParity_spec (n : ℕ) : halfParity n = Nat.pair (n / 2) (n % 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.pair ((halfParity n).unpair.1 + (halfParity n).unpair.2) (1 - (halfParity n).unpair.2)
        = Nat.pair ((n + 1) / 2) ((n + 1) % 2)
    rw [ih, unpair_pair_fst, unpair_pair_snd]
    congr 1 <;> omega

end Domain.Recursive
