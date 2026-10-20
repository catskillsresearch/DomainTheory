module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.SigTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_mem_jc_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_inter_jc_same
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_inter_jc_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jU_inter_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jU_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_subset_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jU_subset_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_subset_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.masterSig_inter_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.masterSig_inter_jc

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

set_option linter.unusedSectionVars false

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

/-- **The `A`-indexed separated sum `𝟙 + Σ_a V`** over `{Λ} ∪ {tu} ∪ ⋃_a aΔ`, under the standing
assumption that no neighbourhood of `V` is empty. The alphabet-generic analogue of `sum3 unitSys V V`
(Example 6.2). -/
def sumSig (A : Type) [DecidableEq A] (V : NeighborhoodSystem β)
    (h : ∀ X, V.mem X → X.Nonempty) :
    NeighborhoodSystem (SigTok A β) where
  mem W := W = masterSig V ∨ W = jU ∨ ∃ a X, V.mem X ∧ W = jc a X
  master := masterSig V
  master_nonempty := ⟨none, none_mem_masterSig⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | rfl | ⟨a, X, hX, rfl⟩)
    · exact subset_rfl
    · exact jU_subset_masterSig
    · exact jc_subset_masterSig hX
  inter_mem := by
    have hne : ∀ W, (W = masterSig V ∨ W = jU ∨ ∃ a X, V.mem X ∧ W = jc a X) →
        (W : Set (SigTok A β)).Nonempty := by
      rintro W (rfl | rfl | ⟨a, X, hX, rfl⟩)
      · exact ⟨none, none_mem_masterSig⟩
      · exact jU_nonempty
      · exact jc_nonempty (h X hX)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | rfl | ⟨a, X, hX, rfl⟩
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [masterSig_inter_jU]; exact Or.inr (Or.inl rfl)
      · rw [masterSig_inter_jc hX']; exact Or.inr (Or.inr ⟨a', X', hX', rfl⟩)
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · rw [Set.inter_comm, masterSig_inter_jU]; exact Or.inr (Or.inl rfl)
      · rw [Set.inter_self]; exact Or.inr (Or.inl rfl)
      · rw [jU_inter_jc] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · rw [Set.inter_comm, masterSig_inter_jc hX]; exact Or.inr (Or.inr ⟨a, X, hX, rfl⟩)
      · rw [Set.inter_comm, jU_inter_jc] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · by_cases haa : a = a'
        · subst haa
          rw [jc_inter_jc_same] at hZsub ⊢
          rcases hZ with rfl | rfl | ⟨a₂, Z₂, hZ₂, rfl⟩
          · exact absurd (hZsub none_mem_masterSig) (by simp)
          · exact absurd (hZsub (show tu ∈ jU from rfl)) tu_not_mem_jc
          · by_cases ha₂ : a = a₂
            · subst ha₂
              exact Or.inr (Or.inr ⟨a, X ∩ X', V.inter_mem hX hX' hZ₂ (jc_subset_jc.mp hZsub), rfl⟩)
            · obtain ⟨t, ht⟩ := h Z₂ hZ₂
              exact absurd (hZsub (tc_mem_jc.mpr ht)) (tc_mem_jc_ne (Ne.symm ha₂))
        · rw [jc_inter_jc_ne haa] at hZsub ⊢
          obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)

end SumSig

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
