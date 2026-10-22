module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.InS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_concat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.nonempty

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap

/-- Intersection of two members of `S` is again in `S` when a consistency witness exists. -/
theorem Ssys_inter_mem {X Y Z : Set (List Bool)}
    (hX : InS X) (hY : InS Y) (hZ : InS Z) (hZsub : Z ⊆ X ∩ Y) : InS (X ∩ Y) :=
  InS.inter hX hY (hZ.nonempty.mono hZsub)

end Exercise722

end DomainTheory.NeighbourhoodSystems
