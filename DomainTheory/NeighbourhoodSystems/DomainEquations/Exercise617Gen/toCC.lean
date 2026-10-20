module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Strn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_inter_jc_same
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_subset_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.masterSig_inter_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.masterSig_inter_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.eq_masterSig_of_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumSig_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjU_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjC_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumMapSig_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tsigObj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tsigMapHom_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Tsig_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Tsig_map_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA_inter_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn_embA_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.singleton_nil_inter_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.CCn

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

set_option linter.unusedSectionVars false

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- **Forward half of `Cₐ ≅ 𝟙 + Σ_a Cₐ`.** Records, for each branch, whether `x` finishes at `Λ`
(the `𝟙`-summand) or reaches the `a`-copy `aX` (the `a`-th summand). -/
def toCC (x : (Cn A).Element) : (CCn A).Element where
  mem W := W = masterSig (Cn A)
    ∨ (W = jU ∧ x.mem ({[]} : Set (Strn A)))
    ∨ (∃ a X, (Cn A).mem X ∧ W = jc a X ∧ x.mem (embA a X))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨a, X, hX, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨a, X, hX, rfl, hzF⟩)
      (rfl | ⟨rfl, hzU'⟩ | ⟨a', X', hX', rfl, hzF'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨by rw [masterSig_inter_jU], hzU'⟩)
    · exact Or.inr (Or.inr ⟨a', X', hX', by rw [masterSig_inter_jc hX'], hzF'⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_comm, masterSig_inter_jU], hzU⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_self], hzU⟩)
    · exfalso
      have hx := x.inter_mem hzU hzF'; rw [singleton_nil_inter_embA] at hx
      obtain ⟨t, ht⟩ := Cn_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨a, X, hX, by rw [Set.inter_comm, masterSig_inter_jc hX], hzF⟩)
    · exfalso
      have hx := x.inter_mem hzF hzU'; rw [Set.inter_comm, singleton_nil_inter_embA] at hx
      obtain ⟨t, ht⟩ := Cn_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · by_cases haa : a = a'
      · subst haa
        have hx := x.inter_mem hzF hzF'; rw [embA_inter] at hx
        exact Or.inr (Or.inr ⟨a, X ∩ X', memCn_embA_inv (x.sub hx), jc_inter_jc_same a X X', hx⟩)
      · exfalso
        have hx := x.inter_mem hzF hzF'; rw [embA_inter_ne haa] at hx
        obtain ⟨t, ht⟩ := Cn_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨a, X, hX, rfl, hzF⟩) hW' hsub
    · exact Or.inl (eq_masterSig_of_subset hsub ((CCn A).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hzU⟩)
      · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        obtain ⟨t', he, -⟩ := hsub (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective he
        exact Or.inr (Or.inr ⟨a, X', hX', rfl,
          x.up_mem hzF (memCn_embA a hX') (embA_subset.mpr (jc_subset_jc.mp hsub))⟩)

end Iso

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
