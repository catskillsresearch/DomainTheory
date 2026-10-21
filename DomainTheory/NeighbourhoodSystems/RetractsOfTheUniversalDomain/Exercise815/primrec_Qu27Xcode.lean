/-ai
If the basic-neighbourhood enumeration is primitive recursive, then the code that folds that enumeration into a universal-domain index is primitive recursive.

It is the code fold of the primitive-recursive intersection step, with zero as the auxiliary function, the master index as the starting value, and the identity as the list code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.primrec_QstepFn

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}


section UniversalSubsystem


theorem primrec_Q'Xcode {r : ℕ → ℕ} (hr : Nat.Primrec r) : Nat.Primrec (Q'Xcode r) :=
  primrec_foldCode (primrec_QstepFn hr) (Nat.Primrec.const 0)
    (Nat.Primrec.const UComputablePresentation.masterIdx) Nat.Primrec.id

end UniversalSubsystem
end DomainTheory.NeighbourhoodSystems
