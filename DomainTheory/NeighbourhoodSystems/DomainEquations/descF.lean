/-ai
The successor operation for a bit on the carrier of a target algebra sends an element to the image, under the structure map, of the second sum injection of that element when the bit is true, and of the first sum injection when the bit is false.
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj1_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj2_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_map_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.ccEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- The `b`-th successor operation `f_b = k ∘ inj_b`: `f₀` via the `0`-copy (`inj₁`), `f₁` via the
`1`-copy (`inj₂`). -/
def descF (b : Bool) (y : B.carrier.sys.Element) : B.carrier.sys.Element :=
  B.str.1.toElementMap (cond b
    (sinj2 (h₀ := Example62C.unitSys_nonempty) (h₁ := B.carrier.nonempty) (h₂ := B.carrier.nonempty) y)
    (sinj1 (h₀ := Example62C.unitSys_nonempty) (h₁ := B.carrier.nonempty) (h₂ := B.carrier.nonempty) y))

end Initial

end DomainTheory.NeighbourhoodSystems
