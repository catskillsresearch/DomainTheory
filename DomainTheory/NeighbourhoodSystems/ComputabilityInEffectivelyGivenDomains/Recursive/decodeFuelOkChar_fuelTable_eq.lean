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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.fuelTable_eq_of_recursion

@[expose] public section


namespace Domain.Recursive


























































































































































































theorem decodeFuelOkChar_fuelTable_eq :
    ∀ fuel bound c, c ≤ bound →
      nthCode (fuelTable decodeFuelOkCharLookup bound fuel) c 0 = decodeFuelOkChar fuel c :=
  fuelTable_eq_of_recursion (F := decodeFuelOkChar) (Body := decodeFuelOkCharBody)
    (fun _ => rfl) (fun _ _ => rfl)
    (fun table c => by unfold decodeFuelOkCharLookup; simp)
    decodeFuelOkCharBody_local

end Domain.Recursive
