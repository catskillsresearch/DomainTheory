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


theorem primrec_decodeFuelOkChar : ∀ fuel, Nat.Primrec (fun c => decodeFuelOkChar fuel c)
  | 0 => Nat.Primrec.const 0
  | fuel + 1 => by
    simpa [decodeFuelOkChar] using
      primrec_decodeFuelOkCharBody (primrec_decodeFuelOkChar fuel)

end Domain.Recursive
