/-ai
consStep2 is primitive recursive.

The left component and the first component of the right half are primitive recursive projections. Successor after their pairing agrees with consStep2 by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.Basic

@[expose] public section


namespace Domain.Recursive


theorem primrec_consStep2 : Nat.Primrec consStep2 := by
  have h1 : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have h21 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  exact (Nat.Primrec.succ.comp (h1.pair h21)).of_eq fun _ => rfl

end Domain.Recursive
