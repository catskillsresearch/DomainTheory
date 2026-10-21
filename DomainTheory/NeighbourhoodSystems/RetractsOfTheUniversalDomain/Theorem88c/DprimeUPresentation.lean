/-ai
The computable presentation of the subsystem DprimeU enumerates the transferred neighbourhoods of the re-pointed enumeration. The neighbourhood at n belongs by the index n, and every neighbourhood of the subsystem arises in this way. Equality of an intersection with a third neighbourhood is the decidable intersection relation, and consistency of a pair is the decidable consistency relation. The intersection index is the intersection index of the re-pointed presentation, which is primitive recursive and correct for the transferred neighbourhoods. The master index is 0.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.DprimeU_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.DprimeU_cons_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.DprimeU_inter_spec

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **Part 6's final assembly.** Theorem 8.8(a)'s own subsystem `DprimeU D (e P) (hcover P) (he0 P)`
(no new construction — the *same* classical `D'`, built via `splitChoice`, that already witnesses
`D ≅ᴰ D'` and `D' ◁ U`) is **effectively given**: its enumeration is `Yidx (e P)` (classical, exactly
like `unitPresentation`'s constant `X`), and its two index relations reduce, via the transfer lemmas
above, to facts already decided by `P0 P`'s own deciders and Part 5's `DAtom_recDecidable`. -/
noncomputable def DprimeUPresentation :
    ComputablePresentation (DprimeU D (e P) (hcover P) (he0 P)) where
  X n := Yidx (e P) n
  mem_X n := ⟨n, rfl⟩
  surj := fun hY => hY.imp (fun _ h => h.symm)
  interEq_computable := DprimeU_interEq_computable P
  cons_computable := DprimeU_cons_computable P
  inter n m := (P0 P).inter n m
  inter_primrec := (P0 P).inter_primrec
  inter_spec h := DprimeU_inter_spec P h
  masterIdx := 0
  masterIdx_spec := Yidx_zero D (e P) (hcover P) (he0 P)

end DomainTheory.NeighbourhoodSystems
