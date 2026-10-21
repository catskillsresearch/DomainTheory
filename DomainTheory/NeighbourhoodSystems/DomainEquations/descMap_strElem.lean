/-ai
The descent map sends the distinguished-string element of a finite string to the recursive value of the distinguished point along that string.

This is the distinguished-string clause of the lifting along C.
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

@[simp] theorem descMap_strElem (σ : Str) :
    (descMap B).toElementMap (strElem σ) = descVal B (descE B) σ :=
  liftC_strElem _ _ _ _ _ σ

end Initial

end DomainTheory.NeighbourhoodSystems
