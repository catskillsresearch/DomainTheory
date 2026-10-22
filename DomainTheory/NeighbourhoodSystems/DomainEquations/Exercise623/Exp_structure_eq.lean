module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.mem_gColim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim_obj_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Texp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Texp_rooted
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Exp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **The domain equation `Exp ≅ N ⊕ ((Exp×Exp)+(Exp×Exp))`**, realised as an equality of systems
(the structure map is the identity). This is the "construe the initial solution" half of
Exercise 6.23. -/
theorem Exp_structure_eq (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    (Texp N).obj (Exp N hN) = Exp N hN :=
  gColim_obj_eq (Texp N) (Texp_rooted hN)

end Exercise619

end DomainTheory.NeighbourhoodSystems
