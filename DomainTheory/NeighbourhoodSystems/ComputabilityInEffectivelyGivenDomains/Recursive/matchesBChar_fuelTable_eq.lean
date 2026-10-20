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

















































































































































































































































open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

































theorem matchesBChar_fuelTable_eq :
    ∀ fuel bound code, code ≤ bound →
      nthCode (fuelTable matchesBCharBodyLookup bound fuel) code 0 =
        matchesBChar fuel code.unpair.1 code.unpair.2 :=
  fuelTable_eq_of_recursion
    (F := fun fuel code => matchesBChar fuel code.unpair.1 code.unpair.2)
    (Body := fun prev code => matchesBCharBody prev code.unpair.1 code.unpair.2)
    (fun _ => rfl) (fun _ _ => rfl)
    (fun table code => by unfold matchesBCharBodyLookup; simp)
    (fun f g code h => matchesBCharBody_local f g code.unpair.1 code.unpair.2 (by
      simpa [pair_unpair] using h))

end Domain.Recursive
