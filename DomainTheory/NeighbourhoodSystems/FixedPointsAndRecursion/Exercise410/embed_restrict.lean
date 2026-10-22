module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.restrict

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem embed_restrict (a : V.Element) (x : V.Element) (hx : x ≤ a) :
    embed a (restrict a x hx) = x := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hVX, W, _, hxW, hWX⟩
    exact x.up_mem hxW hVX hWX
  · intro hxX
    exact ⟨x.sub hxX, X, hx _ hxX, hxX, subset_rfl⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
