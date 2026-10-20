module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **`∃ k, Yidx (e P) k ⊆ Yidx (e P) i ∩ Yidx (e P) j` is recursively decidable in `(i, j)`.** This
transfers (`embed_subset_iff`, twice) to `∃ k, e P k ⊆ e P i ∧ e P k ⊆ e P j`, which is literally
`(P0 P).cons_computable`'s own predicate — reused with no new `Nat.Primrec` work. -/
theorem DprimeU_cons_computable :
    RecDecidable₂ (fun i j => ∃ k, Yidx (e P) k ⊆ Yidx (e P) i ∩ Yidx (e P) j) := by
  refine RecDecidable.of_iff (fun t => ?_) (P0 P).cons_computable
  simp only [Set.subset_inter_iff]
  exact exists_congr (fun k => by
    rw [← embed_subset_iff (e P) k t.unpair.1, ← embed_subset_iff (e P) k t.unpair.2])

end DomainTheory.NeighbourhoodSystems
