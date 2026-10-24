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

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example44

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB


/-- `bx` on a partial element: `b(σ⊥) = (bσ)⊥`. -/
theorem consMap_strBot (b : Bool) (σ : Str) :
    (consMap b).toElementMap (strBot σ) = strBot (b :: σ) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : prepend [b] (cone σ) ⊆ Y := (prepend_mono [b] hXX').trans hsub
    rwa [prepend_cone] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨cone σ, ⟨memC_cone σ, subset_rfl⟩, memC_cone σ, hY, ?_⟩
    rw [prepend_cone]; exact hsub

end DomainTheory.NeighbourhoodSystems.Example44
