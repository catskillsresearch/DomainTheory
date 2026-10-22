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


/-- Primitive-recursive `if` on a `{0,1}` condition. -/
theorem primrec_ite {c t f : ℕ → ℕ} (hc : Nat.Primrec c) (ht : Nat.Primrec t) (hf : Nat.Primrec f) :
    Nat.Primrec (fun n => selectFn (c n) (t n) (f n)) :=
  primrec_selectFn hc ht hf

end Domain.Recursive
