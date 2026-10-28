module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_22

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition_6_6

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510
namespace Exercise619
variable {A₀ A₁ B₀ B₁ : ScottSys}
section Uniqueness
variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)
variable (B : TAlgebra (TexpF N))

def ExpInitial : IsInitial (ExpAlg N hN) where
  desc B := descAlgHom hN B
  uniq B g := algHom_ext (Subtype.ext (descMap_eq_algHom hN B g))

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

theorem Subsystem.proj_isStrict {α : Type*} {D E : NeighborhoodSystem α} (h : D ◁ E) :
    IsStrict h.proj := by
  intro X hrel
  rw [Subsystem.proj_rel] at hrel
  obtain ⟨_, hXD, hsub⟩ := hrel
  exact Set.Subset.antisymm (D.sub_master hXD) (by rw [h.master_eq]; exact hsub)

theorem expHom_comp_expInv (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    (expHom N hN).comp (expInv N hN) = idMap (Exp N hN).sys := by
  have h := congrArg (Subtype.val) (ExpIso N hN).inv_hom_id
  exact h

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

theorem algHom_fix (g : AlgHom (ExpAlg N hN) B) :
    g.hom.1 = (algStr B).comp (((Texp N).map g.hom.1).comp (expInv N hN)) := by
  have hcomm : (g.hom.1).comp (expHom N hN) = (algStr B).comp ((Texp N).map g.hom.1) :=
    congrArg Subtype.val g.comm
  calc g.hom.1
      = (g.hom.1).comp (idMap (Exp N hN).sys) := (comp_idMap _).symm
    _ = (g.hom.1).comp ((expHom N hN).comp (expInv N hN)) := by rw [expHom_comp_expInv]
    _ = ((g.hom.1).comp (expHom N hN)).comp (expInv N hN) := (comp_assoc _ _ _).symm
    _ = ((algStr B).comp ((Texp N).map g.hom.1)).comp (expInv N hN) :=
          congrArg (fun m => m.comp (expInv N hN)) hcomm
    _ = (algStr B).comp (((Texp N).map g.hom.1).comp (expInv N hN)) := comp_assoc _ _ _

theorem descRel_le_algHom (g : AlgHom (ExpAlg N hN) B) : ∀ n, descRel hN B n ≤ g.hom.1
  | 0 => constBot_le _
  | n + 1 => by
      rw [descRel_succ, algHom_fix hN B g]
      exact comp_mono_gen le_rfl
        (comp_mono_gen ((Texp N).map_mono (descRel_le_algHom g n)) le_rfl)

theorem descMap_le_algHom (g : AlgHom (ExpAlg N hN) B) : descMap hN B ≤ g.hom.1 := by
  intro X Y hr
  obtain ⟨n, hn⟩ := hr
  exact descRel_le_algHom hN B g n X Y hn

end Existence

end Exercise619
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise619
section
set_option linter.unusedVariables false

theorem example_623 : ∀ {N : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys}
  (hN :
    @Membership.mem (List Bool) (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (@Set.instMembership DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master DomainTheory.NeighbourhoodSystems.ExampleB.Str
        N.sys)
      (@List.nil Bool))
  (B :
    @DomainTheory.NeighbourhoodSystems.TAlgebra DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
      DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
      (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N))
  (g :
    @DomainTheory.NeighbourhoodSystems.AlgHom DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
      DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
      (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N)
      (DomainTheory.NeighbourhoodSystems.Exercise619.ExpAlg N hN) B),
  @LE.le
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str (DomainTheory.NeighbourhoodSystems.Exercise619.Exp N hN).sys
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
          DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
          (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys)
    (@Preorder.toLE
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str (DomainTheory.NeighbourhoodSystems.Exercise619.Exp N hN).sys
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
            DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
            (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys)
      (@PartialOrder.toPreorder
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str (DomainTheory.NeighbourhoodSystems.Exercise619.Exp N hN).sys
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
              DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
              (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys)
        (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.Exp N hN).sys
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
              DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
              (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys)))
    (@DomainTheory.NeighbourhoodSystems.Exercise619.descMap N hN B)
    (@Subtype.val
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
            DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
            (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N)
            (DomainTheory.NeighbourhoodSystems.Exercise619.ExpAlg N hN)).sys
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
            DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
            (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys)
      (fun
          (f :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier
                  DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
                  DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
                  (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N)
                  (DomainTheory.NeighbourhoodSystems.Exercise619.ExpAlg N hN)).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier
                  DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
                  DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
                  (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys) =>
        @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
              DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
              (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N)
              (DomainTheory.NeighbourhoodSystems.Exercise619.ExpAlg N hN)).sys
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
              DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
              (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys
          f)
      (@DomainTheory.NeighbourhoodSystems.AlgHom.hom DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
        DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
        (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N)
        (DomainTheory.NeighbourhoodSystems.Exercise619.ExpAlg N hN) B g)) :=
  @DomainTheory.NeighbourhoodSystems.Exercise619.descMap_le_algHom
end

end DomainTheory.NeighbourhoodSystems.Exercise619
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

section
namespace Exercise624

def Fsol (D E : ScottSys) : ScottSys := D.sum (D.prod E)

def Gsol (D E : ScottSys) : ScottSys := D.sum E

def gTok (p q : Set Str) : Set Str := insert ([] : Str) (embBit false p ∪ embBit true q)

def fTok (p q : Set Str) : Set Str := gTok p (gTok p q)

def pIter : ℕ → Set Str × Set Str
  | 0 => ({([] : Str)}, {([] : Str)})
  | n + 1 => (fTok (pIter n).1 (pIter n).2, gTok (pIter n).1 (pIter n).2)

def GammaD : Set Str := ⋃ n, (pIter n).1

def GammaE : Set Str := ⋃ n, (pIter n).2

theorem nil_mem_GammaD : ([] : Str) ∈ GammaD := Set.mem_iUnion.mpr ⟨0, rfl⟩

def Dsol : ScottSys := singletonSys GammaD ⟨[], nil_mem_GammaD⟩

theorem nil_mem_GammaE : ([] : Str) ∈ GammaE := Set.mem_iUnion.mpr ⟨0, rfl⟩

def Esol : ScottSys := singletonSys GammaE ⟨[], nil_mem_GammaE⟩

theorem gTok_mono {p p' q q' : Set Str} (hp : p ⊆ p') (hq : q ⊆ q') : gTok p q ⊆ gTok p' q' := by
  rintro w (rfl | ⟨w', rfl, hw'⟩ | ⟨w', rfl, hw'⟩)
  · exact Set.mem_insert _ _
  · exact Or.inr (Or.inl ⟨w', rfl, hp hw'⟩)
  · exact Or.inr (Or.inr ⟨w', rfl, hq hw'⟩)

theorem fTok_mono {p p' q q' : Set Str} (hp : p ⊆ p') (hq : q ⊆ q') : fTok p q ⊆ fTok p' q' :=
  gTok_mono hp (gTok_mono hp hq)

theorem master_Fsol : (Fsol Dsol Esol).sys.master = fTok GammaD GammaE := rfl

theorem master_Gsol : (Gsol Dsol Esol).sys.master = gTok GammaD GammaE := rfl

theorem nil_mem_fTok (p q : Set Str) : ([] : Str) ∈ fTok p q := Set.mem_insert _ _

theorem nil_mem_gTok (p q : Set Str) : ([] : Str) ∈ gTok p q := Set.mem_insert _ _

theorem mem_fTok_iUnion {a b : ℕ → Set Str} {w : Str}
    (hw : w ∈ fTok (⋃ n, a n) (⋃ n, b n)) : ∃ n, w ∈ fTok (a n) (b n) := by
  rcases hw with rfl | ⟨w', rfl, hw'⟩ | ⟨u, rfl, hu⟩
  · exact ⟨0, nil_mem_fTok _ _⟩
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw'
    exact ⟨n, Or.inr (Or.inl ⟨w', rfl, hn⟩)⟩
  · rcases hu with rfl | ⟨u', rfl, hu'⟩ | ⟨u', rfl, hu'⟩
    · exact ⟨0, Or.inr (Or.inr ⟨[], rfl, nil_mem_gTok _ _⟩)⟩
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hu'
      exact ⟨n, Or.inr (Or.inr ⟨false :: u', rfl, Or.inr (Or.inl ⟨u', rfl, hn⟩)⟩)⟩
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hu'
      exact ⟨n, Or.inr (Or.inr ⟨true :: u', rfl, Or.inr (Or.inr ⟨u', rfl, hn⟩)⟩)⟩

theorem mem_gTok_iUnion {a b : ℕ → Set Str} {w : Str}
    (hw : w ∈ gTok (⋃ n, a n) (⋃ n, b n)) : ∃ n, w ∈ gTok (a n) (b n) := by
  rcases hw with rfl | ⟨w', rfl, hw'⟩ | ⟨w', rfl, hw'⟩
  · exact ⟨0, nil_mem_gTok _ _⟩
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw'
    exact ⟨n, Or.inr (Or.inl ⟨w', rfl, hn⟩)⟩
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw'
    exact ⟨n, Or.inr (Or.inr ⟨w', rfl, hn⟩)⟩

theorem pIter_fst_subset_GammaD (m : ℕ) : (pIter m).1 ⊆ GammaD :=
  fun _ hx => Set.mem_iUnion.mpr ⟨m, hx⟩

theorem pIter_snd_subset_GammaE (m : ℕ) : (pIter m).2 ⊆ GammaE :=
  fun _ hx => Set.mem_iUnion.mpr ⟨m, hx⟩

theorem fTok_GammaD_GammaE : fTok GammaD GammaE = GammaD := by
  apply Set.Subset.antisymm
  · intro w hw
    obtain ⟨n, hn⟩ :=
      mem_fTok_iUnion (a := fun n => (pIter n).1) (b := fun n => (pIter n).2) hw
    exact Set.mem_iUnion.mpr ⟨n + 1, hn⟩
  · intro w hw
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
    cases n with
    | zero =>
        have hw0 : w = [] := hn; subst hw0; exact nil_mem_fTok _ _
    | succ m =>
        exact fTok_mono (pIter_fst_subset_GammaD m) (pIter_snd_subset_GammaE m) hn

theorem Dsol_subsystem : Dsol.sys ◁ (Fsol Dsol Esol).sys := by
  have hmaster : (Fsol Dsol Esol).sys.master = GammaD := master_Fsol.trans fTok_GammaD_GammaE
  refine ⟨hmaster.symm, ?_, ?_⟩
  · intro X hX
    have hXeq : X = GammaD := hX
    rw [hXeq, ← hmaster]
    exact (Fsol Dsol Esol).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = GammaD
    rw [show X = GammaD from hX, show Y = GammaD from hY, Set.inter_self]

theorem gTok_GammaD_GammaE : gTok GammaD GammaE = GammaE := by
  apply Set.Subset.antisymm
  · intro w hw
    obtain ⟨n, hn⟩ :=
      mem_gTok_iUnion (a := fun n => (pIter n).1) (b := fun n => (pIter n).2) hw
    exact Set.mem_iUnion.mpr ⟨n + 1, hn⟩
  · intro w hw
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
    cases n with
    | zero =>
        have hw0 : w = [] := hn; subst hw0; exact nil_mem_gTok _ _
    | succ m =>
        exact gTok_mono (pIter_fst_subset_GammaD m) (pIter_snd_subset_GammaE m) hn

theorem Esol_subsystem : Esol.sys ◁ (Gsol Dsol Esol).sys := by
  have hmaster : (Gsol Dsol Esol).sys.master = GammaE := master_Gsol.trans gTok_GammaD_GammaE
  refine ⟨hmaster.symm, ?_, ?_⟩
  · intro X hX
    have hXeq : X = GammaE := hX
    rw [hXeq, ← hmaster]
    exact (Gsol Dsol Esol).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = GammaE
    rw [show X = GammaE from hX, show Y = GammaE from hY, Set.inter_self]

theorem exists_double_fixedPoint :
    ∃ Γd Γe : Set Str, ([] : Str) ∈ Γd ∧ ([] : Str) ∈ Γe ∧
      fTok Γd Γe = Γd ∧ gTok Γd Γe = Γe :=
  ⟨GammaD, GammaE, nil_mem_GammaD, nil_mem_GammaE, fTok_GammaD_GammaE, gTok_GammaD_GammaE⟩

end Exercise624
end
end DomainTheory.NeighbourhoodSystems
end
