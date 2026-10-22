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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.existsListStp_eq

@[expose] public section


namespace Domain.Recursive


theorem existsListChar_eq (g : ℕ → ℕ) (p c : ℕ) :
    existsListChar g p c
      = List.foldl (fun acc x => selectFn acc 1 (isOne (g (Nat.pair x p)))) 0 (decodeList c) := by
  have hfun : (fun (acc x : ℕ) => existsListStp g (Nat.pair x (Nat.pair acc p)))
      = (fun acc x => selectFn acc 1 (isOne (g (Nat.pair x p)))) := by
    funext acc x; exact existsListStp_eq g acc x p
  unfold existsListChar; rw [foldCode_eq', hfun]

end Domain.Recursive
