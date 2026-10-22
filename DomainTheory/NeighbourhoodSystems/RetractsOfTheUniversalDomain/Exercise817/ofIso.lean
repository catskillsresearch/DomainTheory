module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.ProjPair

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Subsystemu2etrianglelefteq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj_comp_inj
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- **A `DomainIso` gives a `ProjPair`, via Theorem 2.7's `ofIso`.** Both round trips are genuine
*equalities* (not just `≤`), since `e` is a full isomorphism, not merely a retraction. Uses
`le_iff_toElementMap_le` (choice-free) rather than the classical `ext_of_toElementMap` — matching
`Theorem86.lean`'s `isRetraction_subApprox`, which flags the same discipline. -/
def ProjPair.ofIso {D : NeighborhoodSystem α} {E : NeighborhoodSystem β} (e : DomainIso D E) :
    ProjPair D E where
  inj := ApproximableMap.ofIso e
  proj := ApproximableMap.ofIso e.symm
  proj_comp_inj := by
    have heq : ∀ x, ((ApproximableMap.ofIso e.symm).comp (ApproximableMap.ofIso e)).toElementMap x
        = (idMap D).toElementMap x := by
      intro x
      rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, OrderIso.symm_apply_apply,
        toElementMap_idMap]
    exact le_antisymm (le_iff_toElementMap_le.mpr fun x => (heq x).le)
      (le_iff_toElementMap_le.mpr fun x => (heq x).ge)
  inj_comp_proj_le := by
    have heq : ∀ y, ((ApproximableMap.ofIso e).comp (ApproximableMap.ofIso e.symm)).toElementMap y
        = (idMap E).toElementMap y := by
      intro y
      rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, OrderIso.apply_symm_apply,
        toElementMap_idMap]
    exact le_iff_toElementMap_le.mpr fun y => (heq y).le

end DomainTheory.NeighbourhoodSystems
