module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGetStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- `listGet` is primitive recursive (on the `Nat.pair` coding of `c, i`). -/
theorem primrec_listGet : Nat.Primrec (fun p => listGet p.unpair.1 p.unpair.2) := by
  have hstp : Nat.Primrec listGetStp := by
    unfold listGetStp
    have hcd : Nat.Primrec (fun t => t.unpair.2.unpair.1.unpair.1) :=
      Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)
    have hval : Nat.Primrec (fun t => t.unpair.2.unpair.1.unpair.2) :=
      Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)
    have hx : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
    exact (primrec_sub₂ hcd (Nat.Primrec.const 1)).pair
      (primrec_selectFn (primrec_isOne.comp hcd) hx hval)
  have hz : Nat.Primrec (fun p : ℕ => Nat.pair (p.unpair.2 + 1) 0) :=
    (Nat.Primrec.succ.comp Nat.Primrec.right).pair (Nat.Primrec.const 0)
  exact (Nat.Primrec.right.comp
    (primrec_foldCode hstp (Nat.Primrec.const 0) hz Nat.Primrec.left)).of_eq fun p => rfl

end Proposition77

end DomainTheory.NeighbourhoodSystems
