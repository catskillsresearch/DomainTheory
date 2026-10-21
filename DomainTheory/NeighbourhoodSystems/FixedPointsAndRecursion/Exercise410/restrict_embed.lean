/-ai
Restricting the embedding of a relativized filter recovers that filter.

Extensionality compares membership. A neighbourhood of the restricted embedding is an enlargement of a neighbourhood of the filter by a set that belongs to a, so upward closure of the filter applies. Conversely, a neighbourhood of the filter belongs to a and witnesses itself as a neighbourhood of the embedding.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.restrict
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed_le

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem restrict_embed (a : V.Element) (g : (relSystem a).Element) :
    restrict a (embed a g) (embed_le a g) = g := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hVX, W, haW, hgW, hWX⟩
    exact g.up_mem hgW (a.up_mem haW hVX hWX) hWX
  · intro hgX
    exact ⟨a.sub (g.sub hgX), X, g.sub hgX, hgX, subset_rfl⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
