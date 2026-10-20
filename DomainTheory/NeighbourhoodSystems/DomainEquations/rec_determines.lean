module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import DomainTheory.NeighbourhoodSystems.DomainEquations.StrictDomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Inst3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tcObj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumMap3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj1_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj2_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_map_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.ccEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descE
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descVal
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617.descMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_strBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_strElem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.genKey
public import DomainTheory.NeighbourhoodSystems.DomainEquations.genKey0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.genKeyBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- **Any map satisfying the homomorphism recursion equals `descMap`.** This is *both* the existence
witness (`descMap` satisfies it) and the uniqueness driver. -/
theorem rec_determines (g : ApproximableMap C B.carrier.sys)
    (hg : g = (B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g)).comp (ofIso ccEquiv)) :
    g = descMap B := by
  have hbot : ∀ σ, g.toElementMap (strBot σ) = descVal B B.carrier.sys.bot σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply]
      exact genKeyBot B g
    | cons b σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply,
        ← consMap_strBot]
      have h := genKey B g b (strBot σ)
      rw [ih] at h
      exact h
  have helem : ∀ σ, g.toElementMap (strElem σ) = descVal B (descE B) σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply]
      exact genKey0 B g
    | cons b σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply,
        ← consMap_strElem]
      have h := genKey B g b (strElem σ)
      rw [ih] at h
      exact h
  apply map_ext_C
  · intro σ; rw [hbot, descMap_strBot]
  · intro σ; rw [helem, descMap_strElem]

end Initial

end DomainTheory.NeighbourhoodSystems
