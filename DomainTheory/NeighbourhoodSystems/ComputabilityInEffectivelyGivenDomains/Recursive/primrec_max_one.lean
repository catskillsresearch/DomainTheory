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


/-- `Nat.max n 1` is primitive recursive. -/
theorem primrec_max_one : Nat.Primrec (fun n => Nat.max n 1) := by
  refine (primrec_selectFn (primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) primrec_id))
    (Nat.Primrec.const 1) primrec_id).of_eq fun n => by
    unfold selectFn isOne Nat.max
    rcases n with _ | n <;> simp

end Domain.Recursive
