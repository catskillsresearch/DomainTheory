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


theorem decodeFuelOkChar_le_one : ∀ fuel c, decodeFuelOkChar fuel c ≤ 1
  | 0, _ => by simp [decodeFuelOkChar]
  | fuel + 1, c => by
    rw [decodeFuelOkChar, decodeFuelOkCharBody_eq]
    match tag : c.unpair.1 with
    | 0 =>
      simp
      rcases (show isOne (1 - c.unpair.2) = 0 ∨ isOne (1 - c.unpair.2) = 1 by
        have := isOne_le_one (1 - c.unpair.2); omega) with h0 | h1
      · rw [h0, selectFn_zero]; exact Nat.zero_le 1
      · rw [h1, selectFn_one]
    | 1 =>
      simp
      exact allBinDigitsChar_le_one _
    | 2 | 3 =>
      simp
      exact mulBit_le_one (decodeFuelOkChar_le_one fuel c.unpair.2.unpair.1)
        (decodeFuelOkChar_le_one fuel c.unpair.2.unpair.2)
    | _ + 4 =>
      simp

end Domain.Recursive
