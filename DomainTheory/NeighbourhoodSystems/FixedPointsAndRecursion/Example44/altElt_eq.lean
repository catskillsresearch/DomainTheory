module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.strBot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.consMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.altElt
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.prepend_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.prepend_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC_cone
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.singleton_subset_cone
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.singleton_cone_nd
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.nestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC_prepend

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.toElementMap_fixElement
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example44

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB


/-- `a = 0(1a)`: `altElt` satisfies Scott's defining equation. -/
theorem altElt_eq : (consMap false).toElementMap ((consMap true).toElementMap altElt) = altElt := by
  have h := toElementMap_fixElement ((consMap false).comp (consMap true))
  rwa [toElementMap_comp] at h

end DomainTheory.NeighbourhoodSystems.Example44
