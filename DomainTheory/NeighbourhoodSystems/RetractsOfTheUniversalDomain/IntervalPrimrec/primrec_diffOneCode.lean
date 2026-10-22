module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem primrec_diffOneCode : Nat.Primrec diffOneCode := by
  have ha : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hb : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hc : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hd : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have hleft : Nat.Primrec (fun t : ℕ =>
      Nat.pair t.unpair.2.unpair.1 (ratMinCode (Nat.pair t.unpair.2.unpair.2 t.unpair.1.unpair.1))) :=
    ha.pair (primrec_ratMinCode.comp (hb.pair hc))
  have hright : Nat.Primrec (fun t : ℕ =>
      Nat.pair (ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2)) t.unpair.2.unpair.2) :=
    (primrec_ratMaxCode.comp (ha.pair hd)).pair hb
  exact (Nat.Primrec.succ.comp (hleft.pair
    (Nat.Primrec.succ.comp (hright.pair (Nat.Primrec.const 0))))).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems
