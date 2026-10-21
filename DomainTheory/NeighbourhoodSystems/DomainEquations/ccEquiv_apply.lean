/-ai
The domain-equation equivalence sends an element of C to its image under the conversion into the sum system.

The two sides are definitionally equal.
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

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


namespace Example62C

open Example44 ExampleB Example62

@[simp] theorem ccEquiv_apply (x : C.Element) : ccEquiv x = toCC x := rfl

end Example62C

end DomainTheory.NeighbourhoodSystems
