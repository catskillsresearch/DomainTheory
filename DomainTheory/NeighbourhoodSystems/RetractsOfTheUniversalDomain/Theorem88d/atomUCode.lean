module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateRem_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.statePos_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateNeg_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateCode_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCodeState

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **The depth-`n` `U`-side code**, for bit-source `k` (meaningful exactly when the matching
`D`-side atom, `DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k))`, is
non-empty — see `genAtom_atomUCode` below). -/
noncomputable def atomUCode (n k : ℕ) : ℕ := stateCode (atomUCodeState P (Nat.pair k n))

end DomainTheory.NeighbourhoodSystems
