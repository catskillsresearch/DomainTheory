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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.fuelTable_eq_of_recursion

@[expose] public section


namespace Domain.Recursive


open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722


theorem autStateCardFuelChar_fuelTable_eq :
    ∀ fuel bound c, c ≤ bound →
      nthCode (fuelTable autStateCardFuelCharLookup bound fuel) c 0 = autStateCardFuelChar fuel c :=
  fuelTable_eq_of_recursion (F := autStateCardFuelChar) (Body := autStateCardFuelCharBody)
    (fun _ => rfl) (fun _ _ => rfl)
    (fun table c => by unfold autStateCardFuelCharLookup; simp)
    autStateCardFuelCharBody_local

end Domain.Recursive
