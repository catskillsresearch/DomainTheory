/-ai
The negative-list code is primitive recursive.

Pairing the third component of a triple code with zero and then adding one is primitive recursive. The equation for the list code of a singleton shows that this function is the negative-list code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.capNegCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.capNegCode_eq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem primrec_capNegCode : Nat.Primrec capNegCode := by
  have hinner : Nat.Primrec (fun t : ℕ => Nat.pair (t.unpair.2.unpair.2) 0) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  refine (primrec_add₂ hinner (Nat.Primrec.const 1)).of_eq (fun t => ?_)
  show _ = capNegCode t
  rw [capNegCode, capNegCode_eq]

end DomainTheory.NeighbourhoodSystems
