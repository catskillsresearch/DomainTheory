/-ai
The depth-n U-side code, read from a packed pair of the depth and the bit-source, is primitive recursive.

It is the code projection of the state recursion applied to the pair of the second component and the first, and that composite equals the stated function.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_stateCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_atomUCodeState

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)






theorem primrec_atomUCode : Nat.Primrec (fun t : ℕ => atomUCode P t.unpair.1 t.unpair.2) :=
  (primrec_stateCode.comp (primrec_atomUCodeState P |>.comp
    (Nat.Primrec.right.pair Nat.Primrec.left))).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems
