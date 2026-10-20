module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive










theorem primrec_qpCombineBop : Nat.Primrec qpCombineBop := by
  have h11 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have h12 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have h21 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h22 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact ((primrec_ratMaxCode.comp (h11.pair h21)).pair
    (primrec_ratMinCode.comp (h12.pair h22))).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems
