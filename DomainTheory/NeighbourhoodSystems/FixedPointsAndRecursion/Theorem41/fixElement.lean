module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_succ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.rel_master_mono

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Theorem 4.1 (Scott 1981, PRG-19).** The least fixed point of `f`, Scott's
`x = {X ∈ 𝒟 ∣ Δ fⁿ X for some n}`. The three filter conditions are exactly Scott's: `Δ ∈ x` (the
`n = 0` witness `I_𝒟`); closure under intersection follows from intersectivity (`inter_right`) of
the single iterate `f^{max n m}` reached by extending the shorter chain; upward closure is `mono`. -/
def fixElement (f : ApproximableMap V V) : V.Element where
  mem X := ∃ n, (f.iterMap n).rel V.master X
  sub := fun ⟨n, h⟩ => (f.iterMap n).rel_cod h
  master_mem := ⟨0, show (idMap V).rel V.master V.master from (idMap V).master_rel⟩
  inter_mem := by
    rintro X Y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, ?_⟩
    have hX : (f.iterMap (max n m)).rel V.master X := rel_master_mono f (le_max_left n m) hn
    have hY : (f.iterMap (max n m)).rel V.master Y := rel_master_mono f (le_max_right n m) hm
    exact (f.iterMap (max n m)).inter_right hX hY
  up_mem := by
    rintro X Y ⟨n, hn⟩ hYmem hXY
    exact ⟨n, (f.iterMap n).mono hn subset_rfl hXY V.master_mem hYmem⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
