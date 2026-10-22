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


/-- `Nat.rec 1 (· * b)` computes `b ^ e` (choice-free). -/
theorem recPow_eq (b : ℕ) :
    ∀ e, Nat.rec (motive := fun _ => ℕ) 1 (fun _ ih => ih * b) e = b ^ e
  | 0 => (pow_zero b).symm
  | e + 1 => by rw [pow_succ]; exact congrArg (· * b) (recPow_eq b e)

end Domain.Recursive
