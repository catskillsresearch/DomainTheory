/-ai
For every real t at most 1, the cut element of t is a fixed point of a.

Compare membership of intervals [0, s) by the endpoint extensionality of R. Membership after applying a means that some interval [0, r) in the cut is related by a to [0, s). The relation is either a strict step r < s or the diagonal r = s = 1. A strict step from a strict cut witness pushes the cut inequality forward to s, while a strict step from the endpoint r = 1 would force 1 < s, contradicting s ≤ 1. The diagonal case puts s = 1 in the cut. Conversely, a strict cut witness at s is preceded, by density of the rationals, by a positive rational r at most 1 with 1 − t < r < s, and [0, r) is then strictly related to [0, s). If s = 1, the interval [0, 1) lies in the cut and is diagonally related to itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.aRel_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.ext_U
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.mkElement_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_Ico0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU_pos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU_le1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- **`cutElt t` is a fixed point of `a`**, for every `t ∈ [0,1]`: this is exactly the "open cut"
computation — `a` shifts `[0,r)` strictly forward, so `s` re-enters the up-set from below iff some
smaller `r` was already in it, i.e. iff `1 - t < s` (density of `ℚ` supplies the witness `r`). -/
theorem toElementMap_cutElt {t : ℝ} (ht1 : t ≤ 1) :
    a.toElementMap (cutElt t ht1) = cutElt t ht1 := by
  apply Element.ext_U
  intro s
  simp only [mem_toElementMap, a_rel, cutElt_mem]
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨r, hUr, rfl⟩ := hX
    have hs01 := R_mem_Ico0 (a.rel_cod (a_rel.mpr hrel))
    rw [aRel_iff (cutU_pos ht1 hUr) (cutU_le1 hUr) hs01.1 hs01.2] at hrel
    rcases hrel with hlt | ⟨hr1, hs1⟩
    · rcases hUr.2 with hc | hr1
      · exact ⟨hs01.2, Or.inl (lt_trans hc (by exact_mod_cast hlt))⟩
      · exact absurd (hr1 ▸ hlt : (1:ℚ) < s) (not_lt.mpr hs01.2)
    · exact ⟨hs01.2, Or.inr hs1⟩
  · intro hs
    rcases hs.2 with hc | rfl
    · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hc
      have hr0 : 0 < r := by
        have : (0:ℝ) ≤ 1 - t := by linarith
        exact_mod_cast lt_of_le_of_lt this hr1
      have hrle1 : r ≤ 1 := by
        have : (r:ℝ) < (s:ℝ) := hr2
        have hrs : r < s := by exact_mod_cast this
        exact hrs.le.trans hs.1
      exact ⟨Set.Ico 0 r, ⟨r, ⟨hrle1, Or.inl hr1⟩, rfl⟩, r, s, hr0, hrle1, cutU_pos ht1 hs,
        cutU_le1 hs, rfl, rfl, Or.inl (by exact_mod_cast hr2)⟩
    · exact ⟨Set.Ico 0 1, ⟨1, cutU_one, rfl⟩, 1, 1, one_pos, le_rfl, one_pos, le_rfl, rfl, rfl,
        Or.inr ⟨rfl, rfl⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise811
