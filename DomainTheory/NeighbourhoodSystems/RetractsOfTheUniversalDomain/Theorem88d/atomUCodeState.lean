/-ai
The packed state of a pair of a bit-source and a depth is the primitive recursion that starts from the base state of the bit-source and iterates the one-step transition, using the extracted emptiness decider, once for each depth.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateRem_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.statePos_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateNeg_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateCode_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomBase
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.datomDec

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **The full state recursion**, packing `atomBase`/`atomStep (datomDec P)` via `Nat.Primrec.prec`:
`atomUCodeState P (pair k n)` is the depth-`n` state for bit-source `k`. -/
noncomputable def atomUCodeState (t : ℕ) : ℕ :=
  t.unpair.2.rec (atomBase t.unpair.1) (fun y IH => atomStep (datomDec P) (Nat.pair t.unpair.1 (Nat.pair y IH)))

end DomainTheory.NeighbourhoodSystems
