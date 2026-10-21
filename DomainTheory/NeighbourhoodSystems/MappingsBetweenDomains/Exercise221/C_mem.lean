/-ai
A set of finite binary strings is a neighbourhood of the system C if and only if it satisfies memC.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem C_mem {X : Set Str} : C.mem X ↔ memC X := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise221
