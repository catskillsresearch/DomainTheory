module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixElement
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_succ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.comp_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_mono_map
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iter_comm
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.rel_master_succ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.rel_master_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.mem_fixElement
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixElement_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterElem_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixElement_eq_iSupDirected
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixMap_toElementMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}


open ApproximableMap


/-- **Theorem 4.2(iii) (Scott 1981, PRG-19).** `fix(f) = ⊔ₙ fⁿ(⊥)` (as a directed union). -/
theorem fixMap_eq_iSup (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    (fixMap V).toElementMap φ =
      NeighborhoodSystem.iSupDirected ((toApproxMap φ).iterElem)
        (fun i j => ⟨max i j, iterElem_mono _ (le_max_left i j),
          iterElem_mono _ (le_max_right i j)⟩) := by
  rw [fixMap_toElementMap]
  exact fixElement_eq_iSupDirected (toApproxMap φ)

end DomainTheory.NeighbourhoodSystems
