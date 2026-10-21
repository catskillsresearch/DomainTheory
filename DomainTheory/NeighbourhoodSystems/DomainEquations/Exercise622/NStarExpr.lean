/-ai
The stream expression on a datum domain N sends X to the coalesced sum of N with the smash product of N and X, the right-hand side of N* congruent to N ⊕ (N ⊗ N*).
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621

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

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619

/-- `T(X) = N ⊕ (N ⊗ X)` — the right-hand side of `N* ≅ N ⊕ (N ⊗ N*)`, parametrised by the (rooted)
datum domain `N`. -/
def NStarExpr (N : ScottSys) : GExpr := .oplus (.const N) (.otimes (.const N) .var)

end Exercise619

end DomainTheory.NeighbourhoodSystems
