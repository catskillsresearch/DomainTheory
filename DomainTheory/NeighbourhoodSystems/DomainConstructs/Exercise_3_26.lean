module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_18
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_19
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Definition_3_3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_4
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example_2_3
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise326
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

section
variable {α : Type*}

abbrev TD : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

theorem Tmem_eq_one {C : Set Example12.Token} (hC : Example12.mem C) (h : C ⊆ Example12.one) :
    C = Example12.one := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact absurd (h (Set.mem_univ 0)) (by simp [Example12.one])
  · exact absurd (h (by simp [Example12.zero] : (0 : Example12.Token) ∈ Example12.zero))
      (by simp [Example12.one])
  · rfl

theorem Tmem_eq_zero {C : Set Example12.Token} (hC : Example12.mem C) (h : C ⊆ Example12.zero) :
    C = Example12.zero := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact absurd (h (Set.mem_univ 1)) (by simp [Example12.zero])
  · rfl
  · exact absurd (h (by simp [Example12.one] : (1 : Example12.Token) ∈ Example12.one))
      (by simp [Example12.zero])

def condGuard (V : NeighborhoodSystem α) (W : Set (Example12.Token ⊕ (α ⊕ α))) (Z : Set α) : Prop :=
  (Sum.inl ⁻¹' W = Example12.zero ∧ Sum.inl ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z) ∨
  (Sum.inl ⁻¹' W = Example12.one ∧ Sum.inr ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z) ∨
  (Sum.inl ⁻¹' W = Example12.master ∧ V.master ⊆ Z)
end

section
variable {α : Type*}
variable (V : NeighborhoodSystem α)

theorem cond_components {W : Set (Example12.Token ⊕ (α ⊕ α))}
    (hW : (prod TD (prod V V)).mem W) :
    Example12.mem (Sum.inl ⁻¹' W) ∧
      V.mem (Sum.inl ⁻¹' (Sum.inr ⁻¹' W)) ∧ V.mem (Sum.inr ⁻¹' (Sum.inr ⁻¹' W)) := by
  obtain ⟨C, P, hC, hP, rfl⟩ := hW
  obtain ⟨X, Y, hX, hY, rfl⟩ := hP
  simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
  exact ⟨hC, hX, hY⟩
end

section
variable {α : Type*}

theorem one_ne_master : (Example12.one : Set Example12.Token) ≠ Example12.master := by
  intro h
  have h0 := Set.ext_iff.mp h 0
  simp [Example12.one, Example12.master] at h0

theorem zero_ne_master : (Example12.zero : Set Example12.Token) ≠ Example12.master := by
  intro h
  have h1 := Set.ext_iff.mp h 1
  simp [Example12.zero, Example12.master] at h1
end

section
variable {α : Type*}
variable (V : NeighborhoodSystem α)

theorem condGuard_master {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} (hg : condGuard V W Z)
    (hC : Sum.inl ⁻¹' W = Example12.master) : V.master ⊆ Z := by
  rcases hg with ⟨hC', _⟩ | ⟨hC', _⟩ | ⟨_, h⟩
  · exact absurd (hC.symm.trans hC') zero_ne_master.symm
  · exact absurd (hC.symm.trans hC') one_ne_master.symm
  · exact h
end

section
variable {α : Type*}

theorem zero_ne_one : (Example12.zero : Set Example12.Token) ≠ Example12.one := by
  intro h
  have h0 := Set.ext_iff.mp h 0
  simp [Example12.zero, Example12.one] at h0
end

section
variable {α : Type*}
variable (V : NeighborhoodSystem α)

theorem condGuard_one {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} (hg : condGuard V W Z)
    (hC : Sum.inl ⁻¹' W = Example12.one) : Sum.inr ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z := by
  rcases hg with ⟨hC', _⟩ | ⟨_, h⟩ | ⟨hC', _⟩
  · exact absurd (hC.symm.trans hC') zero_ne_one.symm
  · exact h
  · exact absurd (hC.symm.trans hC') one_ne_master

theorem condGuard_zero {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} (hg : condGuard V W Z)
    (hC : Sum.inl ⁻¹' W = Example12.zero) : Sum.inl ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z := by
  rcases hg with ⟨_, h⟩ | ⟨hC', _⟩ | ⟨hC', _⟩
  · exact h
  · exact absurd (hC.symm.trans hC') zero_ne_one
  · exact absurd (hC.symm.trans hC') zero_ne_master

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

@[simp] theorem cond_rel {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} :
    (cond V).rel W Z ↔ (prod TD (prod V V)).mem W ∧ V.mem Z ∧ condGuard V W Z := Iff.rfl

theorem cond_bot (x y : V.Element) :
    (cond V).toElementMap (pair Example23.botElt (pair x y)) = V.bot := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCbot, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    have hCm : C = Example12.master := hCbot
    rcases hg with ⟨hCz, _⟩ | ⟨hCo, _⟩ | ⟨_, hmZ⟩
    · exact absurd (hCm.symm.trans hCz) zero_ne_master.symm
    · exact absurd (hCm.symm.trans hCo) one_ne_master.symm
    · rw [mem_bot, Set.Subset.antisymm (V.sub_master hZ) hmZ]
  · intro hbZ
    rw [mem_bot] at hbZ
    subst hbZ
    refine ⟨prodNbhd Example12.master (prodNbhd V.master V.master),
      ⟨Example12.master, prodNbhd V.master V.master, rfl,
        ⟨V.master, V.master, x.master_mem, y.master_mem, rfl⟩, rfl⟩,
      prod_mem_prodNbhd Example12.mem_master (prod_mem_prodNbhd V.master_mem V.master_mem),
      V.master_mem, ?_⟩
    exact Or.inr (Or.inr ⟨inl_preimage_prodNbhd _ _, subset_rfl⟩)

theorem cond_false (x y : V.Element) :
    (cond V).toElementMap (pair Example23.falseElt (pair x y)) = y := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCfalse, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    rcases hg with ⟨hCz, _⟩ | ⟨_, hYZ⟩ | ⟨_, hmZ⟩
    · rcases hCfalse with hCm | hCo
      · exact absurd (hCm.symm.trans hCz) zero_ne_master.symm
      · exact absurd (hCo.symm.trans hCz) zero_ne_one.symm
    · exact y.up_mem hYy hZ hYZ
    · rw [Set.Subset.antisymm (V.sub_master hZ) hmZ]; exact y.master_mem
  · intro hyZ
    have hZ : V.mem Z := y.sub hyZ
    refine ⟨prodNbhd Example12.one (prodNbhd V.master Z), ⟨Example12.one, prodNbhd V.master Z,
      Or.inr rfl, ⟨V.master, Z, x.master_mem, hyZ, rfl⟩, rfl⟩,
      prod_mem_prodNbhd Example12.mem_one (prod_mem_prodNbhd V.master_mem hZ), hZ, ?_⟩
    refine Or.inr (Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩)
    rw [inr_preimage_prodNbhd, inr_preimage_prodNbhd]

theorem cond_toElementMap_mem (t : TD.Element) (x y : V.Element) {Z : Set α} :
    ((cond V).toElementMap (pair t (pair x y))).mem Z ↔
      (t.mem Example12.zero ∧ x.mem Z) ∨ (t.mem Example12.one ∧ y.mem Z) ∨ Z = V.master := by
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCt, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨_, hmZ⟩
    · exact Or.inl ⟨hCz ▸ hCt, x.up_mem hXx hZ hXZ⟩
    · exact Or.inr (Or.inl ⟨hCo ▸ hCt, y.up_mem hYy hZ hYZ⟩)
    · exact Or.inr (Or.inr (Set.Subset.antisymm (V.sub_master hZ) hmZ))
  · intro h
    rcases h with ⟨ht0, hxZ⟩ | ⟨ht1, hyZ⟩ | rfl
    · have hZ : V.mem Z := x.sub hxZ
      refine ⟨prodNbhd Example12.zero (prodNbhd Z V.master), ⟨Example12.zero, prodNbhd Z V.master,
        ht0, ⟨Z, V.master, hxZ, y.master_mem, rfl⟩, rfl⟩,
        prod_mem_prodNbhd Example12.mem_zero (prod_mem_prodNbhd hZ V.master_mem), hZ, ?_⟩
      refine Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩
      rw [inr_preimage_prodNbhd, inl_preimage_prodNbhd]
    · have hZ : V.mem Z := y.sub hyZ
      refine ⟨prodNbhd Example12.one (prodNbhd V.master Z), ⟨Example12.one, prodNbhd V.master Z,
        ht1, ⟨V.master, Z, x.master_mem, hyZ, rfl⟩, rfl⟩,
        prod_mem_prodNbhd Example12.mem_one (prod_mem_prodNbhd V.master_mem hZ), hZ, ?_⟩
      refine Or.inr (Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩)
      rw [inr_preimage_prodNbhd, inr_preimage_prodNbhd]
    · refine ⟨prodNbhd Example12.master (prodNbhd V.master V.master),
        ⟨Example12.master, prodNbhd V.master V.master, t.master_mem,
          ⟨V.master, V.master, x.master_mem, y.master_mem, rfl⟩, rfl⟩,
        prod_mem_prodNbhd Example12.mem_master (prod_mem_prodNbhd V.master_mem V.master_mem),
        V.master_mem, ?_⟩
      exact Or.inr (Or.inr ⟨inl_preimage_prodNbhd _ _, subset_rfl⟩)

theorem cond_true (x y : V.Element) :
    (cond V).toElementMap (pair Example23.trueElt (pair x y)) = x := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCtrue, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    rcases hg with ⟨_, hXZ⟩ | ⟨hCo, _⟩ | ⟨_, hmZ⟩
    · exact x.up_mem hXx hZ hXZ
    · rcases hCtrue with hCm | hCz
      · exact absurd (hCm.symm.trans hCo) one_ne_master.symm
      · exact absurd (hCz.symm.trans hCo) zero_ne_one
    · rw [Set.Subset.antisymm (V.sub_master hZ) hmZ]; exact x.master_mem
  · intro hxZ
    have hZ : V.mem Z := x.sub hxZ
    refine ⟨prodNbhd Example12.zero (prodNbhd Z V.master), ⟨Example12.zero, prodNbhd Z V.master,
      Or.inr rfl, ⟨Z, V.master, hxZ, y.master_mem, rfl⟩, rfl⟩,
      prod_mem_prodNbhd Example12.mem_zero (prod_mem_prodNbhd hZ V.master_mem), hZ, ?_⟩
    refine Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩
    rw [inr_preimage_prodNbhd, inl_preimage_prodNbhd]
end

section
set_option linter.unusedVariables false

theorem example_326.{u_1} : And
  (And
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        x)
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.botElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
          DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
        V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
          DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
          DomainTheory.NeighbourhoodSystems.Example23.falseElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
      y) :=
  @And.intro
  (And
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        x)
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.botElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
          DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
        V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
          DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
          DomainTheory.NeighbourhoodSystems.Example23.falseElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
      y)
  (@And.intro
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        x)
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.botElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
    @DomainTheory.NeighbourhoodSystems.Exercise326.cond_true @DomainTheory.NeighbourhoodSystems.Exercise326.cond_bot)
  @DomainTheory.NeighbourhoodSystems.Exercise326.cond_false
end

section
variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

theorem Tmem_ge_master {C : Set Example12.Token} (hC : Example12.mem C)
    (h : Example12.master ⊆ C) : C = Example12.master :=
  Set.Subset.antisymm (Example12.neighborhoodSystem.sub_master hC) h

theorem Tmem_ge_one {C : Set Example12.Token} (hC : Example12.mem C)
    (h : Example12.one ⊆ C) : C = Example12.one ∨ C = Example12.master := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact Or.inr rfl
  · exact absurd (h (by simp [Example12.one] : (1 : Example12.Token) ∈ Example12.one))
      (by simp [Example12.zero])
  · exact Or.inl rfl

theorem Tmem_ge_zero {C : Set Example12.Token} (hC : Example12.mem C)
    (h : Example12.zero ⊆ C) : C = Example12.zero ∨ C = Example12.master := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact absurd (h (by simp [Example12.zero] : (0 : Example12.Token) ∈ Example12.zero))
      (by simp [Example12.one])

def condSumEmb (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ApproximableMap (prod TD (prod V₀ V₁)) (prod TD (prod (sum V₀ V₁ h₀ h₁) (sum V₀ V₁ h₀ h₁))) :=
  paired (proj₀ TD (prod V₀ V₁))
    (paired ((inMap₀ (h₀ := h₀) (h₁ := h₁)).comp ((proj₀ V₀ V₁).comp (proj₁ TD (prod V₀ V₁))))
      ((inMap₁ (h₀ := h₀) (h₁ := h₁)).comp ((proj₁ V₀ V₁).comp (proj₁ TD (prod V₀ V₁)))))

def condSum (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ApproximableMap (prod TD (prod V₀ V₁)) (sum V₀ V₁ h₀ h₁) :=
  (cond (sum V₀ V₁ h₀ h₁)).comp (condSumEmb V₀ V₁ h₀ h₁)

theorem inter_in_oneset {C C' : Set Example12.Token} (hc : C = Example12.master ∨ C = Example12.one)
    (hc' : C' = Example12.master ∨ C' = Example12.one) :
    C ∩ C' = Example12.master ∨ C ∩ C' = Example12.one := by
  rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
  · exact Or.inl (Set.inter_self _)
  · exact Or.inr (Set.univ_inter _)
  · exact Or.inr (Set.inter_univ _)
  · exact Or.inr (Set.inter_self _)

theorem inter_in_zeroset {C C' : Set Example12.Token} (hc : C = Example12.master ∨ C = Example12.zero)
    (hc' : C' = Example12.master ∨ C' = Example12.zero) :
    C ∩ C' = Example12.master ∨ C ∩ C' = Example12.zero := by
  rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
  · exact Or.inl (Set.inter_self _)
  · exact Or.inr (Set.univ_inter _)
  · exact Or.inr (Set.inter_univ _)
  · exact Or.inr (Set.inter_self _)

def whichGuard (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (W : Set (Option (α ⊕ β))) (C : Set Example12.Token) : Prop :=
  ((∃ X, V₀.mem X ∧ W = inj₀ X) ∧ (C = Example12.master ∨ C = Example12.zero)) ∨
  ((∃ Y, V₁.mem Y ∧ W = inj₁ Y) ∧ (C = Example12.master ∨ C = Example12.one)) ∨
  (W = sumMaster V₀ V₁ ∧ C = Example12.master)

theorem whichGuard_left {W : Set (Option (α ⊕ β))} {C : Set Example12.Token} {X : Set α}
    (hg : whichGuard V₀ V₁ W C) (hW : W = inj₀ X) (hX : X.Nonempty) :
    C = Example12.master ∨ C = Example12.zero := by
  rcases hg with ⟨_, hc⟩ | ⟨⟨Y, _, hWY⟩, _⟩ | ⟨hWsm, _⟩
  · exact hc
  · refine absurd (hW.symm.trans hWY) ?_
    intro h; exact not_inj₀_subset_inj₁ hX h.subset
  · refine absurd (hW.symm.trans hWsm) ?_
    intro h; exact none_mem_inj₀ (h ▸ none_mem_sumMaster)

theorem whichGuard_masterC {W : Set (Option (α ⊕ β))} {C : Set Example12.Token}
    (hg : whichGuard V₀ V₁ W C) (hW : W = sumMaster V₀ V₁) : C = Example12.master := by
  rcases hg with ⟨⟨X, _, hWX⟩, _⟩ | ⟨⟨Y, _, hWY⟩, _⟩ | ⟨_, hc⟩
  · refine absurd (hW.symm.trans hWX) ?_
    intro h; exact none_mem_inj₀ (h ▸ none_mem_sumMaster)
  · refine absurd (hW.symm.trans hWY) ?_
    intro h; exact none_mem_inj₁ (h ▸ none_mem_sumMaster)
  · exact hc

theorem whichGuard_right {W : Set (Option (α ⊕ β))} {C : Set Example12.Token} {Y : Set β}
    (hg : whichGuard V₀ V₁ W C) (hW : W = inj₁ Y) (hY : Y.Nonempty) :
    C = Example12.master ∨ C = Example12.one := by
  rcases hg with ⟨⟨X, _, hWX⟩, _⟩ | ⟨_, hc⟩ | ⟨hWsm, _⟩
  · refine absurd (hW.symm.trans hWX) ?_
    intro h; exact not_inj₁_subset_inj₀ hY h.subset
  · exact hc
  · refine absurd (hW.symm.trans hWsm) ?_
    intro h; exact none_mem_inj₁ (h ▸ none_mem_sumMaster)

def whichMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ApproximableMap (sum V₀ V₁ h₀ h₁) TD where
  rel W C := (sum V₀ V₁ h₀ h₁).mem W ∧ Example12.mem C ∧ whichGuard V₀ V₁ W C
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, Example12.mem_master, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  inter_right := by
    rintro W C C' ⟨hW, _, hg⟩ ⟨_, _, hg'⟩
    rcases hg with ⟨⟨X, hX, rfl⟩, hc⟩ | ⟨⟨Y, hY, rfl⟩, hc⟩ | ⟨rfl, hc⟩
    · have hor := inter_in_zeroset hc (whichGuard_left hg' rfl (h₀ X hX))
      refine ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), ?_, Or.inl ⟨⟨X, hX, rfl⟩, hor⟩⟩
      rcases hor with h | h
      · rw [h]; exact Example12.mem_master
      · rw [h]; exact Example12.mem_zero
    · have hor := inter_in_oneset hc (whichGuard_right hg' rfl (h₁ Y hY))
      refine ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), ?_, Or.inr (Or.inl ⟨⟨Y, hY, rfl⟩, hor⟩)⟩
      rcases hor with h | h
      · rw [h]; exact Example12.mem_master
      · rw [h]; exact Example12.mem_one
    · have hc' := whichGuard_masterC hg' rfl
      subst hc; subst hc'
      rw [Set.inter_self]
      exact ⟨Or.inl rfl, Example12.mem_master, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  mono := by
    rintro W W₂ C C₂ ⟨hW, hC, hg⟩ hW₂W hCC₂ hW₂ hC₂
    refine ⟨hW₂, hC₂, ?_⟩
    rcases hg with ⟨⟨X, hX, rfl⟩, hc⟩ | ⟨⟨Y, hY, rfl⟩, hc⟩ | ⟨rfl, hc⟩
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_inj₀ hW₂ hW₂W
      refine Or.inl ⟨⟨X₂, hX₂, rfl⟩, ?_⟩
      rcases hc with rfl | rfl
      · exact Or.inl (Tmem_ge_master hC₂ hCC₂)
      · exact Or.symm (Tmem_ge_zero hC₂ hCC₂)
    · obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_inj₁ hW₂ hW₂W
      refine Or.inr (Or.inl ⟨⟨Y₂, hY₂, rfl⟩, ?_⟩)
      rcases hc with rfl | rfl
      · exact Or.inl (Tmem_ge_master hC₂ hCC₂)
      · exact Or.symm (Tmem_ge_one hC₂ hCC₂)
    · subst hc
      have hC₂m : C₂ = Example12.master := Tmem_ge_master hC₂ hCC₂
      rcases hW₂ with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
      · exact Or.inr (Or.inr ⟨rfl, hC₂m⟩)
      · exact Or.inl ⟨⟨X₂, hX₂, rfl⟩, Or.inl hC₂m⟩
      · exact Or.inr (Or.inl ⟨⟨Y₂, hY₂, rfl⟩, Or.inl hC₂m⟩)

theorem condSumEmb_toElementMap (t : TD.Element) (x : V₀.Element) (y : V₁.Element) :
    (condSumEmb V₀ V₁ h₀ h₁).toElementMap (pair t (pair x y))
      = pair t (pair ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x)
          ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y)) := by
  simp only [condSumEmb, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair]

end
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

theorem condSum_bot (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.botElt (pair x y)) = (sum V₀ V₁ h₀ h₁).bot := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_bot]

theorem condSum_false (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.falseElt (pair x y))
      = (inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_false]

theorem condSum_true (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.trueElt (pair x y))
      = (inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_true]

theorem not_sum_mem_empty : ¬ (sum V₀ V₁ h₀ h₁).mem ∅ := by
  rintro (h | ⟨X, hX, h⟩ | ⟨Y, hY, h⟩)
  · exact absurd (h.symm ▸ none_mem_sumMaster) (Set.notMem_empty _)
  · obtain ⟨a, ha⟩ := inj₀_nonempty (h₀ X hX)
    exact absurd (h ▸ ha) (Set.notMem_empty _)
  · obtain ⟨b, hb⟩ := inj₁_nonempty (h₁ Y hY)
    exact absurd (h ▸ hb) (Set.notMem_empty _)

theorem inMap₀_outMap₀_eq_of_left {x : (sum V₀ V₁ h₀ h₁).Element}
    (hL : ∃ X, V₀.mem X ∧ x.mem (inj₀ X)) :
    (inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap ((outMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x) = x := by
  obtain ⟨X₀, hX₀, hxX₀⟩ := hL
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, ⟨W, hxW, _, _, hLWX⟩, _, hSZ, hinjXZ⟩

    have hxWX₀ : x.mem (W ∩ inj₀ X₀) := x.inter_mem hxW hxX₀
    obtain ⟨X₁, _, hX₁eq⟩ := mem_subset_inj₀ (x.sub hxWX₀) Set.inter_subset_right
    have hX₁X : X₁ ⊆ X := by
      have : leftPart V₀ (W ∩ inj₀ X₀) ⊆ X :=
        (leftPart_mono V₀ Set.inter_subset_left).trans hLWX
      rwa [hX₁eq, leftPart_inj₀] at this
    have : (W ∩ inj₀ X₀) ⊆ Z :=
      hX₁eq ▸ (inj₀_subset_inj₀.mpr hX₁X).trans hinjXZ
    exact x.up_mem hxWX₀ hSZ this
  · intro hxZ
    rcases x.sub hxZ with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    ·
      exact ⟨V₀.master, ⟨sumMaster V₀ V₁, x.master_mem, (sum V₀ V₁ h₀ h₁).master_mem,
        V₀.master_mem, (leftPart_sumMaster V₀ V₁).subset⟩, V₀.master_mem,
        (sum V₀ V₁ h₀ h₁).master_mem, inj₀_subset_sumMaster V₀.master_mem⟩
    ·
      exact ⟨X', ⟨inj₀ X', hxZ, Or.inr (Or.inl ⟨X', hX', rfl⟩), hX', (leftPart_inj₀ V₀ X').subset⟩,
        hX', Or.inr (Or.inl ⟨X', hX', rfl⟩), subset_rfl⟩
    ·
      have := x.inter_mem hxX₀ hxZ
      rw [inj₀_inter_inj₁] at this
      exact absurd (x.sub this) not_sum_mem_empty

theorem inMap₁_outMap₁_eq_of_right {x : (sum V₀ V₁ h₀ h₁).Element}
    (hR : ∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y)) :
    (inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap ((outMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap x) = x := by
  obtain ⟨Y₀, hY₀, hxY₀⟩ := hR
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨Y, ⟨W, hxW, _, _, hRWY⟩, _, hSZ, hinjYZ⟩
    have hxWY₀ : x.mem (W ∩ inj₁ Y₀) := x.inter_mem hxW hxY₀
    obtain ⟨Y₁, _, hY₁eq⟩ := mem_subset_inj₁ (x.sub hxWY₀) Set.inter_subset_right
    have hY₁Y : Y₁ ⊆ Y := by
      have : rightPart V₁ (W ∩ inj₁ Y₀) ⊆ Y :=
        (rightPart_mono V₁ Set.inter_subset_left).trans hRWY
      rwa [hY₁eq, rightPart_inj₁] at this
    have : (W ∩ inj₁ Y₀) ⊆ Z :=
      hY₁eq ▸ (inj₁_subset_inj₁.mpr hY₁Y).trans hinjYZ
    exact x.up_mem hxWY₀ hSZ this
  · intro hxZ
    rcases x.sub hxZ with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · exact ⟨V₁.master, ⟨sumMaster V₀ V₁, x.master_mem, (sum V₀ V₁ h₀ h₁).master_mem,
        V₁.master_mem, (rightPart_sumMaster V₀ V₁).subset⟩, V₁.master_mem,
        (sum V₀ V₁ h₀ h₁).master_mem, inj₁_subset_sumMaster V₁.master_mem⟩
    · have := x.inter_mem hxY₀ hxZ
      rw [Set.inter_comm, inj₀_inter_inj₁] at this
      exact absurd (x.sub this) not_sum_mem_empty
    · exact ⟨Y', ⟨inj₁ Y', hxZ, Or.inr (Or.inr ⟨Y', hY', rfl⟩), hY', (rightPart_inj₁ V₁ Y').subset⟩,
        hY', Or.inr (Or.inr ⟨Y', hY', rfl⟩), subset_rfl⟩

theorem sum_element_trichotomy (x : (sum V₀ V₁ h₀ h₁).Element) :
    (∃ X, V₀.mem X ∧ x.mem (inj₀ X)) ∨ (∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y)) ∨
      (∀ W, x.mem W → W = (sum V₀ V₁ h₀ h₁).master) := by
  by_cases hL : ∃ X, V₀.mem X ∧ x.mem (inj₀ X)
  · exact Or.inl hL
  by_cases hR : ∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y)
  · exact Or.inr (Or.inl hR)
  refine Or.inr (Or.inr ?_)
  intro W hxW
  rcases x.sub hxW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · rfl
  · exact absurd ⟨X, hX, hxW⟩ hL
  · exact absurd ⟨Y, hY, hxW⟩ hR

theorem which_mem_one {x : (sum V₀ V₁ h₀ h₁).Element} :
    ((whichMap V₀ V₁ h₀ h₁).toElementMap x).mem Example12.one
      ↔ ∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y) := by
  constructor
  · rintro ⟨W, hWx, _, _, hg⟩
    rcases hg with ⟨_, hc⟩ | ⟨⟨Y, hY, rfl⟩, _⟩ | ⟨_, hc⟩
    · rcases hc with h | h
      · exact absurd h one_ne_master
      · exact absurd h zero_ne_one.symm
    · exact ⟨Y, hY, hWx⟩
    · exact absurd hc one_ne_master
  · rintro ⟨Y, hY, hWx⟩
    exact ⟨inj₁ Y, hWx, Or.inr (Or.inr ⟨Y, hY, rfl⟩), Example12.mem_one,
      Or.inr (Or.inl ⟨⟨Y, hY, rfl⟩, Or.inr rfl⟩)⟩

theorem which_mem_zero {x : (sum V₀ V₁ h₀ h₁).Element} :
    ((whichMap V₀ V₁ h₀ h₁).toElementMap x).mem Example12.zero
      ↔ ∃ X, V₀.mem X ∧ x.mem (inj₀ X) := by
  constructor
  · rintro ⟨W, hWx, _, _, hg⟩
    rcases hg with ⟨⟨X, hX, rfl⟩, _⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
    · exact ⟨X, hX, hWx⟩
    · rcases hc with h | h
      · exact absurd h zero_ne_master
      · exact absurd h zero_ne_one
    · exact absurd hc zero_ne_master
  · rintro ⟨X, hX, hWx⟩
    exact ⟨inj₀ X, hWx, Or.inr (Or.inl ⟨X, hX, rfl⟩), Example12.mem_zero,
      Or.inl ⟨⟨X, hX, rfl⟩, Or.inr rfl⟩⟩

theorem cond_which (x : (sum V₀ V₁ h₀ h₁).Element) :
    (cond (sum V₀ V₁ h₀ h₁)).toElementMap
        (pair ((whichMap V₀ V₁ h₀ h₁).toElementMap x)
          (pair ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap
                  ((outMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x))
                ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap
                  ((outMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap x)))) = x := by
  apply Element.ext
  intro Z
  rw [cond_toElementMap_mem, which_mem_zero, which_mem_one]
  constructor
  · rintro (⟨hL, ha⟩ | ⟨hR, hb⟩ | rfl)
    · rwa [inMap₀_outMap₀_eq_of_left hL] at ha
    · rwa [inMap₁_outMap₁_eq_of_right hR] at hb
    · exact x.master_mem
  · intro hxZ
    rcases sum_element_trichotomy x with hL | hR | hN
    · exact Or.inl ⟨hL, by rw [inMap₀_outMap₀_eq_of_left hL]; exact hxZ⟩
    · exact Or.inr (Or.inl ⟨hR, by rw [inMap₁_outMap₁_eq_of_right hR]; exact hxZ⟩)
    · exact Or.inr (Or.inr (hN Z hxZ))
end

section
set_option linter.unusedVariables false

theorem example_326_sum.{u_1, u_2} : And
  (And
    (And
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.botElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.falseElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁) y)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt
            (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Option (Sum α β)) V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁) x)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum (Option (Sum α β)) (Option (Sum α β))))
        (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token
          (Sum (Option (Sum α β)) (Option (Sum α β))) DomainTheory.NeighbourhoodSystems.Exercise326.TD
          (@DomainTheory.NeighbourhoodSystems.prod (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
        (@DomainTheory.NeighbourhoodSystems.Exercise326.cond (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token
          (Sum (Option (Sum α β)) (Option (Sum α β))) DomainTheory.NeighbourhoodSystems.Exercise326.TD
          (@DomainTheory.NeighbourhoodSystems.prod (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β))
            DomainTheory.NeighbourhoodSystems.Example12.Token (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD
            (@DomainTheory.NeighbourhoodSystems.Exercise326.whichMap α β V₀ V₁ h₀ h₁) x)
          (@DomainTheory.NeighbourhoodSystems.pair (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Option (Sum α β)) V₀
              (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β)) α
                (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
                (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁) x))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
              (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β)) β
                (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
                (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁) x)))))
      x) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.botElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.falseElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁) y)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt
            (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Option (Sum α β)) V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁) x)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum (Option (Sum α β)) (Option (Sum α β))))
        (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token
          (Sum (Option (Sum α β)) (Option (Sum α β))) DomainTheory.NeighbourhoodSystems.Exercise326.TD
          (@DomainTheory.NeighbourhoodSystems.prod (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
        (@DomainTheory.NeighbourhoodSystems.Exercise326.cond (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token
          (Sum (Option (Sum α β)) (Option (Sum α β))) DomainTheory.NeighbourhoodSystems.Exercise326.TD
          (@DomainTheory.NeighbourhoodSystems.prod (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β))
            DomainTheory.NeighbourhoodSystems.Example12.Token (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD
            (@DomainTheory.NeighbourhoodSystems.Exercise326.whichMap α β V₀ V₁ h₀ h₁) x)
          (@DomainTheory.NeighbourhoodSystems.pair (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Option (Sum α β)) V₀
              (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β)) α
                (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
                (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁) x))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
              (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β)) β
                (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
                (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁) x)))))
      x)
  (@And.intro
    (And
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.botElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.falseElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁) y)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt
            (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Option (Sum α β)) V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁) x))
    (@And.intro
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.botElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.falseElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁) y))
      @DomainTheory.NeighbourhoodSystems.Exercise326.condSum_bot
      @DomainTheory.NeighbourhoodSystems.Exercise326.condSum_false)
    @DomainTheory.NeighbourhoodSystems.Exercise326.condSum_true)
  @DomainTheory.NeighbourhoodSystems.Exercise326.cond_which
end
end DomainTheory.NeighbourhoodSystems.Exercise326
end
