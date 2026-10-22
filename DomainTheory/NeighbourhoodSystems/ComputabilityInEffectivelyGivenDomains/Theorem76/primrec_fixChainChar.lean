module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.primrec_fixStp

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}


variable (P : ComputablePresentation V)


theorem primrec_fixChainChar (fincl : ℕ → ℕ) (hfinclp : Nat.Primrec fincl) :
    Nat.Primrec (fun t => fixChainChar P fincl t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_fixStp fincl hfinclp) Nat.Primrec.left
    (Nat.Primrec.const (Nat.pair P.masterIdx 1)) Nat.Primrec.right).of_eq (fun _ => rfl)

end DomainTheory.NeighbourhoodSystems
