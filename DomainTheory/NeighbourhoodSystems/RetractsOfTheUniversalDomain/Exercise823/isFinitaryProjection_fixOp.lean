module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise816
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.toApproxMap_bot_eq_constMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.isFinitaryProjection_constMap_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.tOp_toApproxMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.iterElem_succu27
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.iterElem_zerou27

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterElem_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.mem_iterElem
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}


/-- **Exercise 8.23, Claim 1.** Provided `t` maps finitary projections to finitary projections,
`‖t‖ = fix(t)` really is a finitary projection. -/
theorem isFinitaryProjection_fixOp (t : ApproximableMap (funSpace E E) (funSpace E E))
    (ht : ∀ a, FinitaryProjection a → FinitaryProjection (tOp t a)) :
    FinitaryProjection (fixOp t) := by
  have hchain : ∀ n, FinitaryProjection (toApproxMap (t.iterElem n)) := by
    intro n
    induction n with
    | zero =>
      rw [iterElem_zero', toApproxMap_bot_eq_constMap]
      exact isFinitaryProjection_constMap_bot E
    | succ k ih =>
      rw [iterElem_succ', ← tOp_toApproxMap t (t.iterElem k)]
      exact ht _ ih
  have hsub : ∀ n, subFilter (t.iterElem n) = t.iterElem n := by
    intro n
    apply toApproxMap_injective
    rw [toApproxMap_subFilter]
    exact sub_eq_self_of_isFinitaryProjection (hchain n)
  have hdir : ∀ i j : ℕ, ∃ k, t.iterElem i ≤ t.iterElem k ∧ t.iterElem j ≤ t.iterElem k :=
    fun i j => ⟨max i j, iterElem_mono t (le_max_left i j), iterElem_mono t (le_max_right i j)⟩
  have hdirSub : ∀ i j : ℕ, ∃ k, subFilter (t.iterElem i) ≤ subFilter (t.iterElem k) ∧
      subFilter (t.iterElem j) ≤ subFilter (t.iterElem k) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdir i j
    refine ⟨k, ?_, ?_⟩
    · rw [hsub i, hsub k]; exact hik
    · rw [hsub j, hsub k]; exact hjk
  have hEq : t.fixElement = iSupDirected t.iterElem hdir := by
    apply NeighborhoodSystem.Element.ext
    intro Z
    rw [mem_fixElement, mem_iSupDirected]
    simp_rw [mem_iterElem]
  have hkey : subFilter t.fixElement = t.fixElement := by
    rw [hEq, subFilter_iSupDirected t.iterElem hdir hdirSub]
    apply NeighborhoodSystem.Element.ext
    intro Z
    rw [mem_iSupDirected, mem_iSupDirected]
    simp_rw [hsub]
  show FinitaryProjection (toApproxMap t.fixElement)
  apply isFinitaryProjection_of_sub_eq_self
  rw [← toApproxMap_subFilter, hkey]

end Exercise823
end DomainTheory.NeighbourhoodSystems
