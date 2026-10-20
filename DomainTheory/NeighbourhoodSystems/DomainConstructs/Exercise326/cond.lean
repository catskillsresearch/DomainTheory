module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.TD
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.Tmem_eq_zero
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.Tmem_eq_one
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.condGuard
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.condGuard_zero
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.condGuard_one
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.condGuard_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_components

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

variable (V : NeighborhoodSystem α)

/-- **Exercise 3.26 (Scott 1981, PRG-19).** The conditional operator `cond : T × D × D → D`. -/
def cond (V : NeighborhoodSystem α) : ApproximableMap (prod TD (prod V V)) V where
  rel W Z := (prod TD (prod V V)).mem W ∧ V.mem Z ∧ condGuard V W Z
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨(prod TD (prod V V)).master_mem, V.master_mem, Or.inr (Or.inr ⟨?_, subset_rfl⟩)⟩
    show Sum.inl ⁻¹' (prod TD (prod V V)).master = Example12.master
    rw [prod_master, inl_preimage_prodNbhd]; rfl
  inter_right := by
    rintro W Z Z' ⟨hW, hZ, hg⟩ ⟨_, hZ', hg'⟩
    obtain ⟨_, hX, hY⟩ := cond_components V hW
    refine ⟨hW, ?_, ?_⟩
    · rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨hCm, hmZ⟩
      · exact V.inter_mem hZ hZ' hX (Set.subset_inter hXZ (condGuard_zero V hg' hCz))
      · exact V.inter_mem hZ hZ' hY (Set.subset_inter hYZ (condGuard_one V hg' hCo))
      · exact V.inter_mem hZ hZ' V.master_mem (Set.subset_inter hmZ (condGuard_master V hg' hCm))
    · rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨hCm, hmZ⟩
      · exact Or.inl ⟨hCz, Set.subset_inter hXZ (condGuard_zero V hg' hCz)⟩
      · exact Or.inr (Or.inl ⟨hCo, Set.subset_inter hYZ (condGuard_one V hg' hCo)⟩)
      · exact Or.inr (Or.inr ⟨hCm, Set.subset_inter hmZ (condGuard_master V hg' hCm)⟩)
  mono := by
    rintro W W₂ Z Z₂ ⟨hW, hZ, hg⟩ hW₂W hZZ₂ hW₂ hZ₂
    obtain ⟨hC₂, hX₂, hY₂⟩ := cond_components V hW₂
    refine ⟨hW₂, hZ₂, ?_⟩
    have hCsub : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
    have hXsub : Sum.inl ⁻¹' (Sum.inr ⁻¹' W₂) ⊆ Sum.inl ⁻¹' (Sum.inr ⁻¹' W) :=
      Set.preimage_mono (Set.preimage_mono hW₂W)
    have hYsub : Sum.inr ⁻¹' (Sum.inr ⁻¹' W₂) ⊆ Sum.inr ⁻¹' (Sum.inr ⁻¹' W) :=
      Set.preimage_mono (Set.preimage_mono hW₂W)
    rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨hCm, hmZ⟩
    · exact Or.inl ⟨Tmem_eq_zero hC₂ (hCsub.trans hCz.subset), (hXsub.trans hXZ).trans hZZ₂⟩
    · exact Or.inr (Or.inl ⟨Tmem_eq_one hC₂ (hCsub.trans hCo.subset),
        (hYsub.trans hYZ).trans hZZ₂⟩)
    · have hmZ₂ : V.master ⊆ Z₂ := hmZ.trans hZZ₂
      rcases (Example12.mem_iff (Sum.inl ⁻¹' W₂)).mp hC₂ with hC₂m | hC₂z | hC₂o
      · exact Or.inr (Or.inr ⟨hC₂m, hmZ₂⟩)
      · exact Or.inl ⟨hC₂z, (V.sub_master hX₂).trans hmZ₂⟩
      · exact Or.inr (Or.inl ⟨hC₂o, (V.sub_master hY₂).trans hmZ₂⟩)

end DomainTheory.NeighbourhoodSystems.Exercise326
