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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.aRel_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.ext_U
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.mkElement_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_Ico0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutS
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutS_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutS_bddBelow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutPoint_le_one

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- **Surjectivity**: every fixed point of `a` equals `cutElt (cutPoint x) _`; the fixed-point
equation supplies exactly the "openness" (no minimum, aside from `r = 1`) that makes this work. -/
theorem cutElt_cutPoint {x : R.Element} (hfix : a.toElementMap x = x) :
    cutElt (cutPoint x) (cutPoint_le_one x) = x := by
  have hSne := cutS_nonempty x
  have hSbdd := cutS_bddBelow x
  apply Element.ext_U
  intro r
  rw [cutElt_mem]
  have hcU : cutU (cutPoint x) r ↔ (r ≤ 1 ∧ (sInf (cutS x) < (r : ℝ) ∨ r = 1)) := by
    unfold cutPoint
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h1, Or.inl (by linarith)⟩
      · exact ⟨h1, Or.inr h2⟩
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h1, Or.inl (by linarith)⟩
      · exact ⟨h1, Or.inr h2⟩
  rw [hcU, Iff.comm]
  have hopen : ∀ Y, x.mem Y ↔ ∃ X, x.mem X ∧ a.rel X Y := by
    intro Y
    conv_lhs => rw [← hfix]
    exact mem_toElementMap a x
  constructor
  · intro hxr
    refine ⟨(R_mem_Ico0 (x.sub hxr)).2, ?_⟩
    by_cases hr1 : r = 1
    · exact Or.inr hr1
    · refine Or.inl ?_
      obtain ⟨X, hXmem, hrel⟩ := (hopen (Set.Ico 0 r)).mp hxr
      obtain ⟨r'', hr''0, hr''1, rfl⟩ := x.sub hXmem
      rw [a_rel, aRel_iff hr''0 hr''1 (R_mem_Ico0 (x.sub hxr)).1 (R_mem_Ico0 (x.sub hxr)).2] at hrel
      rcases hrel with hlt | ⟨-, hreq⟩
      · calc sInf (cutS x) ≤ (r'' : ℝ) := csInf_le hSbdd ⟨r'', hXmem, rfl⟩
          _ < (r : ℝ) := by exact_mod_cast hlt
      · exact absurd hreq hr1
  · rintro ⟨hr1, hc | rfl⟩
    · obtain ⟨q, ⟨r0, hr0mem, rfl⟩, hqlt⟩ := exists_lt_of_csInf_lt hSne hc
      dsimp only at hqlt
      have hr0r : r0 < r := by exact_mod_cast hqlt
      have hr0pos : 0 < r0 := (R_mem_Ico0 (x.sub hr0mem)).1
      exact x.up_mem hr0mem ⟨r, hr0pos.trans hr0r, hr1, rfl⟩ (Set.Ico_subset_Ico le_rfl hr0r.le)
    · rw [← R_master]; exact x.master_mem

end DomainTheory.NeighbourhoodSystems.Exercise811
