/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.idxSet_inter_eq_iff_DAtom
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.DAtom_pair_recDecidable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.inclK_i_recDecidable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.inclK_j_recDecidable

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **Part 6's headline decidability result.** `Yidx (e P) i ∩ Yidx (e P) j = Yidx (e P) k` is
recursively decidable in `(i, j, k)`: it transfers (`transfer_inter_eq_iff`) to the `idxSet`-level
equation, which `idxSet_inter_eq_iff_DAtom` reduces to two `incl_computable` queries and one
`DAtom_recDecidable` query — all already decidable. -/
theorem DprimeU_interEq_computable :
    RecDecidable₃ (fun i j k => Yidx (e P) i ∩ Yidx (e P) j = Yidx (e P) k) := by
  have hcomb : RecDecidable₃ (fun i j k =>
      ((P0 P).X k ⊆ (P0 P).X i ∧ (P0 P).X k ⊆ (P0 P).X j) ∧ DAtom (P0 P) [i, j] [k] = ∅) :=
    (inclK_i_recDecidable P |>.and (inclK_j_recDecidable P)).and (DAtom_pair_recDecidable P)
  refine RecDecidable.of_iff (fun t => ?_) hcomb
  dsimp only
  rw [← transfer_inter_eq_iff splitChoice (idxSet (e P)) Set.univ univ_nonempty_nat
      splitChoice_isSplitSpec t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2
      (Set.subset_univ _) (Set.subset_univ _) (Set.subset_univ _),
    idxSet_inter_eq_iff_DAtom (P0 P) t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2]
  tauto

end DomainTheory.NeighbourhoodSystems
