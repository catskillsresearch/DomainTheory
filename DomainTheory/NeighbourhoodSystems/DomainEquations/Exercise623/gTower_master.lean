module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFix
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gChain

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

/-- Every level of the tower has the same master `Δ = Γ`. -/
theorem gTower_master (T : GExpr) (hT : T.RootedConst) :
    ∀ n, (gTower T n).sys.master = gFix T
  | 0 => rfl
  | n + 1 => ((gChain T hT n).master_eq).symm.trans (gTower_master T hT n)

end Exercise619

end DomainTheory.NeighbourhoodSystems
