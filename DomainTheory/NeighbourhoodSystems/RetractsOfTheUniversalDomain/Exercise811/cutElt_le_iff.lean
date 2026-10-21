/-ai
For reals t and t' in the unit interval, the cut element of t lies below the cut element of t' if and only if t ≤ t'.

Order of elements is inclusion of up-sets. If t is not at most t', a rational lies strictly between 1 − t and 1 − t' and is at most 1, so it belongs to the smaller cut and the resulting membership in the larger cut contradicts that upper bound. If t ≤ t', monotonicity of the cut up-set gives the inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
import all Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
import all Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
import all Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import all Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.mkElement_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.le_iff_U
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU_mono

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- **Scott's hint made precise:** `⊆` (the up-sets, i.e. `⊑` on `R.Element`) matches `≤` (on the
represented reals) — `cutElt` is order-preserving *both ways*. -/
theorem cutElt_le_iff {t t' : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ht0' : 0 ≤ t') (ht1' : t' ≤ 1) :
    cutElt t ht1 ≤ cutElt t' ht1' ↔ t ≤ t' := by
  rw [le_iff_U]
  simp only [cutElt_mem]
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show (1 - t : ℝ) < 1 - t' by linarith)
    have hrle1 : r ≤ 1 := by
      have : (r : ℝ) < 1 := by linarith
      exact_mod_cast this.le
    have hcutt' : cutU t' r := h r ⟨hrle1, Or.inl hr1⟩
    rcases hcutt'.2 with hc' | hreq
    · linarith
    · rw [hreq] at hr2; norm_num at hr2; linarith
  · exact fun htt' r hr => cutU_mono htt' hr

end DomainTheory.NeighbourhoodSystems.Exercise811
