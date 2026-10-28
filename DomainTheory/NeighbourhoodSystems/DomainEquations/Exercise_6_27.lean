module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_12
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_26

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition_6_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510
section
namespace Exercise627
variable {D₀ D₁ : NeighborhoodSystem Str}
variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem inl_trianglelefteq_oplus :
    D₀ ⊴ oplusTok D₀ D₁ h₀ h₁ :=
  trianglelefteq_of_projectionPair inlInj inlProj inlProj_comp_inlInj inlInj_comp_inlProj_le

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem ext_of_principal {γ δ : Type*} {W₀ : NeighborhoodSystem γ} {W₁ : NeighborhoodSystem δ}
    {f g : ApproximableMap W₀ W₁}
    (h : ∀ (X : Set γ) (hX : W₀.mem X),
      f.toElementMap (W₀.principal hX) = g.toElementMap (W₀.principal hX)) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  constructor
  · intro hr
    have hX := f.rel_dom hr
    rw [g.rel_iff_mem_principal hX, ← h X hX, ← f.rel_iff_mem_principal hX]; exact hr
  · intro hr
    have hX := g.rel_dom hr
    rw [f.rel_iff_mem_principal hX, h X hX, ← g.rel_iff_mem_principal hX]; exact hr

end Part5

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem fstInj_comp_fstProj_le (D₀ D₁ : NeighborhoodSystem Str) :
    (fstInj D₀ D₁).comp (fstProj D₀ D₁) ≤ idMap (prodTok D₀ D₁) := by
  intro W W' hr
  obtain ⟨X, ⟨hW, _, hsub⟩, _, hW', hsub'⟩ := hr
  exact ⟨hW, hW', hsub.trans hsub'⟩

theorem fstProj_comp_fstInj (D₀ D₁ : NeighborhoodSystem Str) :
    (fstProj D₀ D₁).comp (fstInj D₀ D₁) = idMap D₀ := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨hX, _, hsub⟩, _, hZ, hsub'⟩
    exact ⟨hX, hZ, (prodTokNbhd_subset_iff.mp (hsub.trans hsub')).1⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨prodTokNbhd Z D₁.master,
      ⟨hX, prodTok_mem_prodTokNbhd hZ D₁.master_mem,
        prodTokNbhd_subset_iff.mpr ⟨hXZ, subset_rfl⟩⟩,
      prodTok_mem_prodTokNbhd hZ D₁.master_mem, hZ, subset_rfl⟩

theorem fst_trianglelefteq_prod (D₀ D₁ : NeighborhoodSystem Str) :
    D₀ ⊴ prodTok D₀ D₁ :=
  trianglelefteq_of_projectionPair (fstInj D₀ D₁) (fstProj D₀ D₁)
    (fstProj_comp_fstInj D₀ D₁) (fstInj_comp_fstProj_le D₀ D₁)

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem oplusTok_subsystem_sumTok (h₀ : ∀ X, D₀.mem X → X.Nonempty)
    (h₁ : ∀ Y, D₁.mem Y → Y.Nonempty) :
    oplusTok D₀ D₁ h₀ h₁ ◁ sumTok D₀ D₁ h₀ h₁ where
  master_eq := rfl
  sub := by
    rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
    · exact Or.inl rfl
    · exact sumTok_mem_embF hX
    · exact sumTok_mem_embT hY
  inter_closed := by
    rintro W W' (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
      (rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [sumTokMaster_inter_embF hX']; exact oplusTok_mem_embF hX' hX'ne
    · rw [sumTokMaster_inter_embT hY']; exact oplusTok_mem_embT hY' hY'ne
    · rw [Set.inter_comm, sumTokMaster_inter_embF hX]; exact oplusTok_mem_embF hX hXne
    · rw [embBit_inter] at hInt ⊢
      exact oplusTok_mem_embF (sumTok_mem_embF_inv hInt)
        (inter_ne_of_ne_left (D₀.sub_master hX) hXne)
    · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hInt
      exact absurd (sumTok_mem_nonempty hInt) Set.not_nonempty_empty
    · rw [Set.inter_comm, sumTokMaster_inter_embT hY]; exact oplusTok_mem_embT hY hYne
    · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hInt
      exact absurd (sumTok_mem_nonempty hInt) Set.not_nonempty_empty
    · rw [embBit_inter] at hInt ⊢
      exact oplusTok_mem_embT (sumTok_mem_embT_inv hInt)
        (inter_ne_of_ne_left (D₁.sub_master hY) hYne)

theorem oplus_trianglelefteq_sum (h₀ : ∀ X, D₀.mem X → X.Nonempty)
    (h₁ : ∀ Y, D₁.mem Y → Y.Nonempty) :
    oplusTok D₀ D₁ h₀ h₁ ⊴ sumTok D₀ D₁ h₀ h₁ :=
  (oplusTok_subsystem_sumTok h₀ h₁).trianglelefteq

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem otimesTok_subsystem_prodTok (D₀ D₁ : NeighborhoodSystem Str) :
    otimesTok D₀ D₁ ◁ prodTok D₀ D₁ where
  master_eq := rfl
  sub := by
    rintro W (rfl | ⟨X, Y, hX, hY, -, -, rfl⟩)
    · exact ⟨D₀.master, D₁.master, D₀.master_mem, D₁.master_mem, rfl⟩
    · exact ⟨X, Y, hX, hY, rfl⟩
  inter_closed := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩)
      (rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [prodTokNbhd_inter, Set.inter_eq_right.mpr (D₀.sub_master hX'),
        Set.inter_eq_right.mpr (D₁.sub_master hY')]
      exact Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · rw [Set.inter_comm, prodTokNbhd_inter, Set.inter_eq_right.mpr (D₀.sub_master hX),
        Set.inter_eq_right.mpr (D₁.sub_master hY)]
      exact Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
    · rw [prodTokNbhd_inter] at hInt ⊢
      obtain ⟨A, B, hA, hB, heq⟩ := hInt
      obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
      exact Or.inr ⟨X ∩ X', Y ∩ Y', hA, hB,
        inter_ne_of_ne_left (D₀.sub_master hX) hXne,
        inter_ne_of_ne_left (D₁.sub_master hY) hYne, rfl⟩

theorem otimes_trianglelefteq_prod (D₀ D₁ : NeighborhoodSystem Str) :
    otimesTok D₀ D₁ ⊴ prodTok D₀ D₁ :=
  (otimesTok_subsystem_prodTok D₀ D₁).trianglelefteq

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem otimes_unitPt_collapse :
    ∀ W, (otimesTok twoPt unitPt).mem W → W = (otimesTok twoPt unitPt).master := by
  rintro W (rfl | ⟨X, Y, _, hY, _, hYne, rfl⟩)
  · rfl
  · exact absurd hY hYne

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem strictifyMap_le (g : ApproximableMap V₀ V₁) : strictifyMap g ≤ g := fun _ _ h => h.1

theorem strictifyMap_of_isStrict {f : ApproximableMap V₀ V₁} (hf : IsStrict f) :
    strictifyMap f = f := by
  apply ApproximableMap.ext
  intro X Y
  exact ⟨fun h => h.1, fun h => ⟨h, fun hXm => hf (hXm ▸ h)⟩⟩

end Part5

theorem subsingleton_element_of_only_master {γ : Type*} {V : NeighborhoodSystem γ}
    (h : ∀ X, V.mem X → X = V.master) : Subsingleton V.Element := by
  refine ⟨fun x y => ?_⟩
  apply Element.ext
  intro X
  constructor
  · intro hx; have hXm := h X (x.sub hx); rw [hXm]; exact y.master_mem
  · intro hy; have hXm := h X (y.sub hy); rw [hXm]; exact x.master_mem

theorem not_trianglelefteq_otimes :
    ¬ (twoPt ⊴ otimesTok twoPt unitPt) := by
  rintro ⟨D', hsub, ⟨e⟩⟩
  have hD'only : ∀ X, D'.mem X → X = D'.master := by
    intro X hX
    rw [otimes_unitPt_collapse X (hsub.sub hX)]; exact hsub.master_eq.symm
  have hss : Subsingleton D'.Element := subsingleton_element_of_only_master hD'only
  have hPmem : twoPt.mem ({[]} : Set Str) := Or.inr rfl
  have hne : twoPt.principal hPmem ≠ twoPt.principal twoPt.master_mem := by
    intro heq
    have h1 : (twoPt.principal hPmem).mem ({[]} : Set Str) := ⟨hPmem, subset_rfl⟩
    rw [heq] at h1
    obtain ⟨-, h2⟩ := h1
    exact absurd (Set.mem_singleton_iff.mp (h2 (Set.mem_univ ([false] : Str))) :
      ([false] : Str) = []) (by decide)
  exact hne (e.injective (hss.allEq (e (twoPt.principal hPmem))
    (e (twoPt.principal twoPt.master_mem))))

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem toApproxMap_toFilter (g : ApproximableMap V₀ V₁) : toApproxMap (toFilter g) = g :=
  (funSpaceEquiv V₀ V₁).apply_symm_apply g

theorem toElementMap_inclMap (φ : (strictFun V₀ V₁).Element) :
    inclMap.toElementMap φ = incl φ := by
  apply Element.ext
  intro M
  constructor
  · rintro ⟨W, hφW, _, hincl⟩
    obtain ⟨hMmem, hg⟩ := hincl
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hMmem
    refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    obtain ⟨hsstep, hWsub⟩ := toStrictMap_rel.mp (hg p hp)
    exact φ.up_mem hφW hsstep hWsub
  · rintro ⟨hMmem, hgφ⟩
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hMmem
    have hφL : φ.mem (sstepFun L) :=
      (mem_sstepFun_iff φ hL).mpr (fun p hp => toStrictMap_rel.mp (hgφ p hp))
    refine ⟨sstepFun L, hφL, φ.sub hφL, ⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    exact ⟨φ.sub (toStrictMap_rel.mp (hgφ p hp)), fun f hf => hf p hp⟩

theorem toElementMap_strctMap (ψ : (funSpace V₀ V₁).Element) :
    strctMap.toElementMap ψ = strct ψ := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨M, hψM, _, hstrct⟩
    obtain ⟨hWmem, hg⟩ := hstrct
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hWmem
    refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    obtain ⟨hstepmem, hMsub⟩ := (hg p hp).1
    exact ⟨ψ.up_mem hψM hstepmem hMsub, (hg p hp).2⟩
  · rintro ⟨hWmem, hgψ⟩
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hWmem
    have hψL : ψ.mem (stepFun L) :=
      (mem_stepFun_iff ψ hL).mpr (fun p hp => (hgψ p hp).1)
    refine ⟨stepFun L, hψL, ψ.sub hψL, ⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    exact ⟨⟨ψ.sub (hgψ p hp).1, fun f hf => hf p hp⟩, (hgψ p hp).2⟩

theorem toFilter_toApproxMap (ψ : (funSpace V₀ V₁).Element) : toFilter (toApproxMap ψ) = ψ :=
  (funSpaceEquiv V₀ V₁).symm_apply_apply ψ

theorem toStrictFilter_toStrictMap (φ : (strictFun V₀ V₁).Element) :
    toStrictFilter (toStrictMap φ) = φ :=
  (strictFunEquiv V₀ V₁).symm_apply_apply φ

theorem strct_incl (φ : (strictFun V₀ V₁).Element) : strct (incl φ) = φ := by
  show toStrictFilter (strictify (toApproxMap (toFilter (toStrictMap φ).1))) = φ
  rw [toApproxMap_toFilter,
    show strictify (toStrictMap φ).1 = toStrictMap φ from
      Subtype.ext (strictifyMap_of_isStrict (toStrictMap φ).2)]
  exact toStrictFilter_toStrictMap φ

theorem strctMap_comp_inclMap :
    (strctMap (V₀ := V₀) (V₁ := V₁)).comp inclMap = idMap (strictFun V₀ V₁) := by
  apply ext_of_principal
  intro X hX
  rw [toElementMap_comp, toElementMap_inclMap, toElementMap_strctMap, strct_incl, toElementMap_idMap]

theorem toStrictMap_toStrictFilter (g : StrictMap V₀ V₁) : toStrictMap (toStrictFilter g) = g :=
  (strictFunEquiv V₀ V₁).apply_symm_apply g

theorem incl_strct_le (ψ : (funSpace V₀ V₁).Element) : incl (strct ψ) ≤ ψ := by
  have key : incl (strct ψ) = toFilter (strictifyMap (toApproxMap ψ)) := by
    show toFilter (toStrictMap (strct ψ)).1 = toFilter (strictifyMap (toApproxMap ψ))
    rw [show toStrictMap (strct ψ) = strictify (toApproxMap ψ) from toStrictMap_toStrictFilter _]
    rfl
  rw [key]
  conv_rhs => rw [← toFilter_toApproxMap ψ]
  exact (funSpaceEquiv V₀ V₁).symm.monotone (strictifyMap_le (toApproxMap ψ))

theorem inclMap_comp_strctMap_le :
    (inclMap (V₀ := V₀) (V₁ := V₁)).comp strctMap ≤ idMap (funSpace V₀ V₁) := by
  rw [le_iff_toElementMap_le]
  intro ψ
  rw [toElementMap_comp, toElementMap_strctMap, toElementMap_inclMap, toElementMap_idMap]
  exact incl_strct_le ψ

theorem strictFun_trianglelefteq_funSpace (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    strictFun V₀ V₁ ⊴ funSpace V₀ V₁ :=
  trianglelefteq_of_projectionPair inclMap strctMap strctMap_comp_inclMap inclMap_comp_strctMap_le

end Part5

end Exercise627
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise627
section
set_option linter.unusedVariables false

theorem example_627.{u_1, u_2} : And
  (And
    (And
      (And
        (And
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)))
        (∀
          (D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
            (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)))
      (Not
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
          (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
            DomainTheory.NeighbourhoodSystems.Exercise627.unitPt))))
    (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      (h₀ :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X)
      (h₁ :
        ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₁
              Y →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)
        (DomainTheory.NeighbourhoodSystems.Exercise619.sumTok D₀ D₁ h₀ h₁)))
  (∀ {α : Type u_1} {β : Type u_2} (V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq
      (@DomainTheory.NeighbourhoodSystems.Exercise510.StrictMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.Exercise510.strictFun α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)) :=
  @And.intro
  (And
    (And
      (And
        (And
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)))
        (∀
          (D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
            (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)))
      (Not
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
          (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
            DomainTheory.NeighbourhoodSystems.Exercise627.unitPt))))
    (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      (h₀ :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X)
      (h₁ :
        ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₁
              Y →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)
        (DomainTheory.NeighbourhoodSystems.Exercise619.sumTok D₀ D₁ h₀ h₁)))
  (∀ {α : Type u_1} {β : Type u_2} (V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq
      (@DomainTheory.NeighbourhoodSystems.Exercise510.StrictMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.Exercise510.strictFun α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
  (@And.intro
    (And
      (And
        (And
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)))
        (∀
          (D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
            (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)))
      (Not
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
          (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
            DomainTheory.NeighbourhoodSystems.Exercise627.unitPt))))
    (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      (h₀ :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X)
      (h₁ :
        ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₁
              Y →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)
        (DomainTheory.NeighbourhoodSystems.Exercise619.sumTok D₀ D₁ h₀ h₁))
    (@And.intro
      (And
        (And
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)))
        (∀
          (D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
            (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)))
      (Not
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
          (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
            DomainTheory.NeighbourhoodSystems.Exercise627.unitPt)))
      (@And.intro
        (And
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)))
        (∀
          (D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
            (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
        (@And.intro
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁))
          DomainTheory.NeighbourhoodSystems.Exercise627.otimes_trianglelefteq_prod
          @DomainTheory.NeighbourhoodSystems.Exercise627.inl_trianglelefteq_oplus)
        DomainTheory.NeighbourhoodSystems.Exercise627.fst_trianglelefteq_prod)
      DomainTheory.NeighbourhoodSystems.Exercise627.not_trianglelefteq_otimes)
    @DomainTheory.NeighbourhoodSystems.Exercise627.oplus_trianglelefteq_sum)
  @DomainTheory.NeighbourhoodSystems.Exercise627.strictFun_trianglelefteq_funSpace
end

end DomainTheory.NeighbourhoodSystems.Exercise627
end

section

universe w

namespace DomainTheory.NeighbourhoodSystems
namespace Theorem614

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {α : Type w}

structure Setup where

  T : Endofunctor DomainObj.{w}

  hmaps : ContinuousOnMaps T

  hmono : MonotoneOnDomains T

  hcont : ContinuousOnDomains T
  {Tok : Type w}

  Γ : NeighborhoodSystem Tok

  ceq : (T.obj ⟨Tok, Γ⟩).carrier = Tok

  hsub : Γ ◁ (ceq ▸ (T.obj ⟨Tok, Γ⟩).sys : NeighborhoodSystem Tok)

end Theorem614
end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section
universe w

namespace Theorem614

variable {α : Type w}

theorem mem_cast {β : Type w} (e : β = α) (V : NeighborhoodSystem β) (X : Set α) :
    (e ▸ V : NeighborhoodSystem α).mem X ↔ V.mem (e.symm ▸ X : Set β) := by
  cases e; rfl

theorem rec_trans {β γ : Type w} (e : β = γ) (e' : γ = α) (x : NeighborhoodSystem β) :
    (e' ▸ (e ▸ x : NeighborhoodSystem γ) : NeighborhoodSystem α) = (e.trans e') ▸ x := by
  cases e; cases e'; rfl

theorem set_rec_trans {β γ : Type w} (e : β = γ) (e' : γ = α) (X : Set β) :
    (e' ▸ (e ▸ X : Set γ) : Set α) = (e.trans e') ▸ X := by
  cases e; cases e'; rfl

theorem subsystem_cast {β : Type w} (e : β = α) {D E : NeighborhoodSystem β} (h : D ◁ E) :
    (e ▸ D : NeighborhoodSystem α) ◁ (e ▸ E : NeighborhoodSystem α) := by
  cases e; exact h

def iter (s : Setup.{w}) : (n : ℕ) →
    Σ' (S : NeighborhoodSystem s.Tok), Σ' (ceq : (s.T.obj ⟨s.Tok, S⟩).carrier = s.Tok),
      S ◁ (ceq ▸ (s.T.obj ⟨s.Tok, S⟩).sys : NeighborhoodSystem s.Tok)
  | 0 => ⟨s.Γ, s.ceq, s.hsub⟩
  | (n + 1) =>
      let p := iter s n
      ⟨p.2.1 ▸ (s.T.obj ⟨s.Tok, p.1⟩).sys,
        (s.hmono p.2.2).carrier_eq.trans p.2.1,
        by
          have hsub := subsystem_cast p.2.1 (s.hmono p.2.2).sub
          rwa [rec_trans] at hsub⟩

def Dsys (s : Setup.{w}) (n : ℕ) : NeighborhoodSystem s.Tok := (iter s n).1

theorem Dceq (s : Setup.{w}) (n : ℕ) : (s.T.obj ⟨s.Tok, Dsys s n⟩).carrier = s.Tok := (iter s n).2.1

theorem Dchain (s : Setup.{w}) (n : ℕ) : Dsys s n ◁ Dsys s (n + 1) := (iter s n).2.2

theorem Dsys_master (s : Setup.{w}) (n : ℕ) : (Dsys s n).master = s.Γ.master := by
  induction n with
  | zero => rfl
  | succ k ih => rw [← (Dchain s k).master_eq]; exact ih

theorem Dsys_succ (s : Setup.{w}) (n : ℕ) :
    Dsys s (n + 1) = (Dceq s n ▸ (s.T.obj ⟨s.Tok, Dsys s n⟩).sys : NeighborhoodSystem s.Tok) :=
  rfl

theorem chain_le (s : Setup.{w}) {n m : ℕ} (h : n ≤ m) : Dsys s n ◁ Dsys s m := by
  induction h with
  | refl => exact Subsystem.refl _
  | step _ ih => exact ih.trans (Dchain s _)

def colim (s : Setup.{w}) : NeighborhoodSystem s.Tok where
  mem X := ∃ n, (Dsys s n).mem X
  master := s.Γ.master
  master_nonempty := s.Γ.master_nonempty
  master_mem := ⟨0, s.Γ.master_mem⟩
  inter_mem := by
    rintro X Y Z ⟨n, hX⟩ ⟨m, hY⟩ ⟨p, hZ⟩ hsub
    set N := max n (max m p) with hN
    have hXN : (Dsys s N).mem X := (chain_le s (le_max_left n _)).sub hX
    have hYN : (Dsys s N).mem Y :=
      (chain_le s ((le_max_left m p).trans (le_max_right n _))).sub hY
    have hZN : (Dsys s N).mem Z :=
      (chain_le s ((le_max_right m p).trans (le_max_right n _))).sub hZ
    exact ⟨N, (Dsys s N).inter_mem hXN hYN hZN hsub⟩
  sub_master := by
    rintro X ⟨n, hX⟩
    rw [← Dsys_master s n]
    exact (Dsys s n).sub_master hX

@[simp] theorem mem_colim (s : Setup.{w}) {X : Set s.Tok} :
    (colim s).mem X ↔ ∃ n, (Dsys s n).mem X := Iff.rfl

@[simp] theorem colim_master (s : Setup.{w}) : (colim s).master = s.Γ.master := rfl

theorem Dsys_sub_colim (s : Setup.{w}) (n : ℕ) : Dsys s n ◁ colim s where
  master_eq := by rw [colim_master, Dsys_master]
  sub hX := ⟨n, hX⟩
  inter_closed := by
    rintro X Y hX hY ⟨m, hXY⟩
    have hN : (Dsys s (max n m)).mem (X ∩ Y) := by
      have hle : (Dsys s m) ◁ (Dsys s (max n m)) := chain_le s (le_max_right n m)
      exact hle.sub hXY

    exact (chain_le s (le_max_left n m)).inter_closed hX hY hN

theorem colimCeq (s : Setup.{w}) : (s.T.obj ⟨s.Tok, colim s⟩).carrier = s.Tok :=
  (s.hmono (Dsys_sub_colim s 0)).carrier_eq.trans (Dceq s 0)

def Tcolim (s : Setup.{w}) : NeighborhoodSystem s.Tok :=
  colimCeq s ▸ (s.T.obj ⟨s.Tok, colim s⟩).sys

theorem Dsys_sub_Tcolim (s : Setup.{w}) (n : ℕ) : Dsys s (n + 1) ◁ Tcolim s := by
  have h := subsystem_cast (Dceq s n) (s.hmono (Dsys_sub_colim s n)).sub
  rw [rec_trans] at h
  exact h

theorem Tcolim_master (s : Setup.{w}) : (Tcolim s).master = s.Γ.master := by
  rw [← (Dsys_sub_Tcolim s 0).master_eq, Dsys_master]

theorem Tcolim_sub_colim (s : Setup.{w}) {X : Set s.Tok} (hX : (Tcolim s).mem X) :
    (colim s).mem X := by
  obtain ⟨hmono', hC⟩ := s.hcont
  set ℱ : Set (NeighborhoodSystem s.Tok) := Set.range (Dsys s) with hℱdef
  have hℱ : ∀ ⦃D⦄, D ∈ ℱ → D ◁ colim s := by rintro D ⟨n, rfl⟩; exact Dsys_sub_colim s n
  have hne : ℱ.Nonempty := ⟨Dsys s 0, ⟨0, rfl⟩⟩
  have hdir : DirectedOn (· ◁ ·) ℱ := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    exact ⟨Dsys s (max n m), ⟨max n m, rfl⟩,
      chain_le s (le_max_left n m), chain_le s (le_max_right n m)⟩
  have hU : ∀ Y, (colim s).mem Y ↔ ∃ D ∈ ℱ, D.mem Y := by
    intro Y; constructor
    · rintro ⟨n, hn⟩; exact ⟨Dsys s n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨D, ⟨n, rfl⟩, hn⟩; exact ⟨n, hn⟩
  have heq := hC ℱ hℱ hne hdir (Subsystem.refl (colim s)) hU
  set Y₀ : Set (s.T.obj ⟨s.Tok, colim s⟩).carrier := (colimCeq s).symm ▸ X with hY₀

  have hmem : Y₀ ∈ targetFam s.T hmono' (Subsystem.refl (colim s)) :=
    (mem_cast (colimCeq s) _ X).mp hX
  rw [heq, Set.mem_iUnion] at hmem
  obtain ⟨D, hmem⟩ := hmem
  rw [Set.mem_iUnion] at hmem
  obtain ⟨hD, hmemD⟩ := hmem
  obtain ⟨n, rfl⟩ := hD
  simp only [targetFam, Set.mem_ofPred_eq] at hmemD

  refine ⟨n + 1, ?_⟩
  rw [Dsys_succ s n, mem_cast (Dceq s n)]
  have key : ((Dceq s n).symm ▸ X : Set (s.T.obj ⟨s.Tok, Dsys s n⟩).carrier)
      = (s.hmono (hℱ ⟨n, rfl⟩)).carrier_eq ▸ Y₀ := by
    rw [hY₀, set_rec_trans]
  rw [key]
  exact hmemD

theorem colim_sub_Tcolim (s : Setup.{w}) {X : Set s.Tok} (hX : (colim s).mem X) :
    (Tcolim s).mem X := by
  obtain ⟨n, hn⟩ := hX
  exact (Dsys_sub_Tcolim s n).sub ((Dchain s n).sub hn)

theorem Tcolim_eq_colim (s : Setup.{w}) : Tcolim s = colim s :=
  NeighborhoodSystem.ext
    (fun _ => ⟨fun h => Tcolim_sub_colim s h, fun h => colim_sub_Tcolim s h⟩)
    (by rw [Tcolim_master, colim_master])

theorem domainObj_ext {c : Type w} (σ : NeighborhoodSystem c) (e : c = α)
    {V : NeighborhoodSystem α} (h : (e ▸ σ : NeighborhoodSystem α) = V) :
    (⟨c, σ⟩ : DomainObj) = ⟨α, V⟩ := by
  cases e; cases h; rfl

theorem colimObj_eq (s : Setup.{w}) :
    s.T.obj ⟨s.Tok, colim s⟩ = (⟨s.Tok, colim s⟩ : DomainObj) :=
  domainObj_ext (s.T.obj ⟨s.Tok, colim s⟩).sys (colimCeq s) (Tcolim_eq_colim s)

def isoOfEq {Obj : Type*} [Category Obj] {X Y : Obj} (h : X = Y) : Iso X Y := by
  cases h
  exact ⟨(𝟙 X), (𝟙 X), CategoryTheory.Category.id_comp _, CategoryTheory.Category.id_comp _⟩

def colimIso (s : Setup.{w}) : Iso (s.T.obj ⟨s.Tok, colim s⟩) (⟨s.Tok, colim s⟩ : DomainObj) :=
  isoOfEq (colimObj_eq s)

def rho (s : Setup.{w}) (n : ℕ) : ApproximableMap (colim s) (colim s) :=
  (Dsys_sub_colim s n).inj.comp (Dsys_sub_colim s n).proj

theorem rho_rel (s : Setup.{w}) (n : ℕ) {X Y : Set s.Tok} :
    (rho s n).rel X Y ↔
      (colim s).mem X ∧ (colim s).mem Y ∧ ∃ z, (Dsys s n).mem z ∧ X ⊆ z ∧ z ⊆ Y := by
  unfold rho
  rw [comp_rel]
  constructor
  · rintro ⟨z, ⟨hcX, hDz, hXz⟩, _, hcY, hzY⟩
    exact ⟨hcX, hcY, z, hDz, hXz, hzY⟩
  · rintro ⟨hcX, hcY, z, hDz, hXz, hzY⟩
    exact ⟨z, ⟨hcX, hDz, hXz⟩, hDz, hcY, hzY⟩

theorem rho_mono (s : Setup.{w}) {n m : ℕ} (h : n ≤ m) {X Y : Set s.Tok}
    (hr : (rho s n).rel X Y) : (rho s m).rel X Y := by
  rw [rho_rel] at hr ⊢
  obtain ⟨hcX, hcY, z, hDz, hXz, hzY⟩ := hr
  exact ⟨hcX, hcY, z, (chain_le s h).sub hDz, hXz, hzY⟩

def iSupRho (s : Setup.{w}) : ApproximableMap (colim s) (colim s) :=
  iSupMap (rho s) (fun i j => ⟨max i j,
    fun _ _ h => rho_mono s (le_max_left i j) h,
    fun _ _ h => rho_mono s (le_max_right i j) h⟩)

abbrev colimAlg (s : Setup.{w}) : TAlgebra s.T :=
  ⟨⟨s.Tok, colim s⟩, (colimIso s).hom⟩

abbrev objColim (s : Setup.{w}) : DomainObj := ⟨s.Tok, colim s⟩

abbrev objDsys (s : Setup.{w}) (n : ℕ) : DomainObj := ⟨s.Tok, Dsys s n⟩

abbrev Tmap_rho (s : Setup.{w}) (n : ℕ) :
    ApproximableMap (s.T.obj (objColim s)).sys (s.T.obj (objColim s)).sys :=
  s.T.map (X := objColim s) (Y := objColim s) (rho s n)

@[simp] theorem Dsys_zero (s : Setup.{w}) : Dsys s 0 = s.Γ := rfl

theorem algHom_ext {Obj : Type*} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}
    {g g' : AlgHom A B} (h : g.hom = g'.hom) : g = g' := by
  cases g; cases g'; cases h; rfl

theorem cat_comp_eq {X Y Z : DomainObj} (g : (Y ⟶ Z)) (f : (X ⟶ Y)) :
    g ⊚ f = g.comp f := rfl

theorem iSupRho_eq_id (s : Setup.{w}) : iSupRho s = idMap (colim s) := by
  apply ApproximableMap.ext
  intro X Y
  rw [idMap_rel]
  constructor
  · rintro ⟨n, hr⟩
    rw [rho_rel] at hr
    obtain ⟨hcX, hcY, z, _, hXz, hzY⟩ := hr
    exact ⟨hcX, hcY, hXz.trans hzY⟩
  · rintro ⟨hcX, hcY, hXY⟩
    obtain ⟨n, hX⟩ := hcX
    exact ⟨n, (rho_rel s n).mpr ⟨⟨n, hX⟩, hcY, X, hX, subset_rfl, hXY⟩⟩

theorem isoOfEq_conj {Obj : Type*} [Category Obj] {X Y : Obj} (e : X = Y)
    (f : (X ⟶ X)) :
    (isoOfEq e).hom ⊚ f ⊚ (isoOfEq e).inv = (e ▸ f : (Y ⟶ Y)) := by
  cases e
  change (𝟙 X) ⊚ f ⊚ (𝟙 X) = f
  dsimp only [compAfter]
  rw [CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp]

theorem map_comp_proj_heq {Tok : Type w} {Pc Qc : Type w} (cn : Pc = Tok) (cc : Qc = Tok)
    {Ps : NeighborhoodSystem Pc} {Qs : NeighborhoodSystem Qc} (ce : Qc = Pc)
    (sub : Ps ◁ (ce ▸ Qs : NeighborhoodSystem Pc))
    {Dn1 Col : NeighborhoodSystem Tok}
    (hDn1 : (cn ▸ Ps : NeighborhoodSystem Tok) = Dn1)
    (hCol : (cc ▸ Qs : NeighborhoodSystem Tok) = Col)
    (hsub' : Dn1 ◁ Col)
    (Tmi : ApproximableMap Ps Qs) (Tmj : ApproximableMap Qs Ps)
    (hi : HEq Tmi sub.inj) (hj : HEq Tmj sub.proj) :
    HEq (Tmi.comp Tmj) (hsub'.inj.comp hsub'.proj) := by
  subst cn
  subst cc
  obtain rfl := hDn1
  obtain rfl := hCol
  have e1 : Tmi = sub.inj := eq_of_heq hi
  have e2 : Tmj = sub.proj := eq_of_heq hj
  rw [e1, e2]

theorem map_rho_heq (s : Setup.{w}) (n : ℕ) :
    HEq (Tmap_rho s n) (rho s (n + 1)) := by
  have hcomp : Tmap_rho s n
      = (s.T.map (X := objDsys s n) (Y := objColim s) (Dsys_sub_colim s n).inj).comp
          (s.T.map (X := objColim s) (Y := objDsys s n) (Dsys_sub_colim s n).proj) :=
    s.T.map_comp (X := objColim s) (Y := objDsys s n) (Z := objColim s)
      (Dsys_sub_colim s n).inj (Dsys_sub_colim s n).proj
  rw [hcomp]
  exact map_comp_proj_heq (Dceq s n) (colimCeq s) (s.hmono (Dsys_sub_colim s n)).carrier_eq
    (s.hmono (Dsys_sub_colim s n)).sub (Dsys_succ s n).symm (Tcolim_eq_colim s)
    (Dsys_sub_colim s (n + 1)) (s.T.map (X := objDsys s n) (Y := objColim s) (Dsys_sub_colim s n).inj)
    (s.T.map (X := objColim s) (Y := objDsys s n) (Dsys_sub_colim s n).proj)
    (s.hmono (Dsys_sub_colim s n)).inj_heq (s.hmono (Dsys_sub_colim s n)).proj_heq

theorem nonempty_strict_algHom (s : Setup.{w}) (B : TAlgebra s.T) (hk : IsStrict B.str) :
    Nonempty {g : AlgHom (colimAlg s) B // IsStrict g.hom} :=
  nonempty_algHom_of_continuousOnMaps s.T s.hmaps (colimIso s) B hk

theorem nonempty_algHom (s : Setup.{w}) (B : TAlgebra s.T) (hk : IsStrict B.str) :
    Nonempty (AlgHom (colimAlg s) B) :=
  (nonempty_strict_algHom s B hk).map (·.1)

end Theorem614
end
end DomainTheory.NeighbourhoodSystems
end
