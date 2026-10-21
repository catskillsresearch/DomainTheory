/-ai
The empty string belongs to the fixed-point token set of a grammar expression.

It belongs to the zero iterate, and therefore to the union.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFix

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2emap_comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2emap_continuous
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2emap_continuous_mp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2emap_id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2emap_isStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2emap_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2enaryOp_rootedConst
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2eobj_continuous
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2eobj_continuous_mp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2eobj_subsystem
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

theorem gFix_nil_mem (T : GExpr) : ([] : Str) ∈ gFix T :=
  Set.mem_iUnion.mpr ⟨0, rfl⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
