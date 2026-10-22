module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.mem_iterElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterElem_mono

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Theorem 4.2(iii) (Scott 1981, PRG-19).** `fix(f) = ⊔ₙ fⁿ(⊥)`, here as the directed union of
the increasing chain of approximants. -/
theorem fixElement_eq_iSupDirected (f : ApproximableMap V V) :
    f.fixElement =
      NeighborhoodSystem.iSupDirected (f.iterElem)
        (fun i j => ⟨max i j, iterElem_mono f (le_max_left i j),
          iterElem_mono f (le_max_right i j)⟩) := by
  apply Element.ext
  intro X
  rw [NeighborhoodSystem.mem_iSupDirected]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mpr hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mp hn⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
