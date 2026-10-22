module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_cons
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut_single

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

@[simp] theorem kOut_cons (b c : Bool) (t : Str) : kOut (b :: c :: t) = b :: kOut t := rfl

end DomainTheory.NeighbourhoodSystems.Exercise218
