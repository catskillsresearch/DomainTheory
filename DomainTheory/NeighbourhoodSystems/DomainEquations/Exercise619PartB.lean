/-ai
This file gathers and re-exports the Part B development of Exercise 6.19. It includes the basic setup; strictness, identity, and composition for the token-level sum and product actions on maps; the same three laws for functor expressions; monotonicity of the sum action, the product action, and the expression action; the subsystem laws for the token sum, the token product, and the object action; and continuity of the object action and of the map action, both the forward direction and the full equivalence.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.sumMapTok_isStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.prodMapTok_isStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.sumMapTok_id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.sumMapTok_comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.prodMapTok_id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.prodMapTok_comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.FExpru2emap_isStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.FExpru2emap_id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.FExpru2emap_comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.sumMapTok_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.prodMapTok_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.FExpru2emap_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.sumTok_subsystem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.prodTok_subsystem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.FExpru2eobj_subsystem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.FExpru2eobj_continuous_mp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.FExpru2eobj_continuous
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.FExpru2emap_continuous_mp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.FExpru2emap_continuous

@[expose] public section
