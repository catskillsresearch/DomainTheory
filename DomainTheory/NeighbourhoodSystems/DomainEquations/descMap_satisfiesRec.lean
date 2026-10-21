/-ai
The descent map on C equals the structure map composed with the triple sum of the identity and two copies of the descent map, composed with the domain-equation equivalence.

Compare the maps on bottom-string elements and on distinguished-string elements. On a bottom-string the composite element map is the equivalence application followed by the sum map and the structure map, and the descent map is the recursive value of bottom. The empty string is the bottom key. A cons cell rewrites the equivalence application as the successor of the shorter bottom-string, and the successor key, after the bottom-string evaluation, matches. On a distinguished-string the empty string is the zero key and a cons cell is the successor key after the distinguished-string evaluation.
ai-/
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

/-- `C`'s algebra map satisfies the recursion. -/
theorem descMap_satisfiesRec :
    descMap B = (B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty)
        (h₁ := Example62C.C_nonempty) (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty)
        (h₁' := B.carrier.nonempty) (h₂' := B.carrier.nonempty) (idMap unitSys) (descMap B)
        (descMap B))).comp (ofIso ccEquiv) := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strBot]
    cases σ with
    | nil => exact (genKeyBot B (descMap B)).symm
    | cons b σ =>
      rw [Example62C.ccEquiv_apply, ← consMap_strBot]
      have h := genKey B (descMap B) b (strBot σ)
      rw [descMap_strBot] at h
      exact h.symm
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strElem]
    cases σ with
    | nil => exact (genKey0 B (descMap B)).symm
    | cons b σ =>
      rw [Example62C.ccEquiv_apply, ← consMap_strElem]
      have h := genKey B (descMap B) b (strElem σ)
      rw [descMap_strElem] at h
      exact h.symm

end Initial

end DomainTheory.NeighbourhoodSystems
