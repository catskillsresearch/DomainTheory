module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_12
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_21

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition_6_6

@[expose] public section

section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619

def Cnat : ScottSys where
  sys :=
    { mem := fun X => X = {([false] : Str)} ∨ X = {([false] : Str), ([] : Str)}
      master := {([false] : Str), ([] : Str)}
      master_nonempty := ⟨[false], Set.mem_insert _ _⟩
      master_mem := Or.inr rfl
      inter_mem := by
        have hAB : ({([false] : Str)} : Set Str) ⊆ {([false] : Str), ([] : Str)} :=
          Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
        rintro X Y Z (rfl | rfl) (rfl | rfl) _ _
        · exact Or.inl (Set.inter_self _)
        · exact Or.inl (Set.inter_eq_self_of_subset_left hAB)
        · exact Or.inl (Set.inter_eq_self_of_subset_right hAB)
        · exact Or.inr (Set.inter_self _)
      sub_master := by
        have hAB : ({([false] : Str)} : Set Str) ⊆ {([false] : Str), ([] : Str)} :=
          Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
        rintro X (rfl | rfl)
        · exact hAB
        · exact subset_rfl }
  ne := by
    rintro X (rfl | rfl)
    · exact ⟨[false], rfl⟩
    · exact ⟨[false], Set.mem_insert _ _⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

section
namespace Exercise619

def Cone : ScottSys := singletonSys ({([] : Str)} : Set Str) ⟨[], rfl⟩

def MExpr : GExpr := .sum (.const Cone) .var

def NExpr : GExpr := .oplus (.const Cnat) .var

def NStarExpr (N : ScottSys) : GExpr := .oplus (.const N) (.otimes (.const N) .var)

theorem NStarExpr_rooted {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) :
    (NStarExpr N).RootedConst := ⟨hN, hN, trivial⟩

theorem NStar_eq_solution (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ ((NStarExpr N).obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem (NStarExpr N) (NStarExpr_rooted hN)

theorem nil_mem_Cnat : ([] : Str) ∈ Cnat.sys.master := Set.mem_insert_iff.mpr (Or.inr rfl)

theorem NExpr_rooted : NExpr.RootedConst := ⟨nil_mem_Cnat, trivial⟩

theorem NStar_over_N_exists :
    ∃ N : ScottSys, ([] : Str) ∈ N.sys.master ∧
      ∃ (Γ : Set Str) (h : Γ.Nonempty),
        (singletonSys Γ h).sys ◁ ((NStarExpr N).obj (singletonSys Γ h)).sys := by
  obtain ⟨Γ₁, hnil₁, _⟩ := gExists_tok_fixedPoint NExpr NExpr_rooted
  exact ⟨singletonSys Γ₁ ⟨[], hnil₁⟩, hnil₁, NStar_eq_solution _ hnil₁⟩

end Exercise619
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise619
section
set_option linter.unusedVariables false

theorem example_622 : ∃ (N : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys),
  And
    (@Membership.mem (List Bool) (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (@Set.instMembership DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master DomainTheory.NeighbourhoodSystems.ExampleB.Str
        N.sys)
      (@List.nil Bool))
    (∃ (Γ : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str) (h :
      @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Γ),
      @DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (DomainTheory.NeighbourhoodSystems.Exercise619.singletonSys Γ h).sys
        ((DomainTheory.NeighbourhoodSystems.Exercise619.NStarExpr N).obj
            (DomainTheory.NeighbourhoodSystems.Exercise619.singletonSys Γ h)).sys) :=
  DomainTheory.NeighbourhoodSystems.Exercise619.NStar_over_N_exists
end

end DomainTheory.NeighbourhoodSystems.Exercise619
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619

theorem N_eq_solution :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (NExpr.obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem NExpr NExpr_rooted

theorem nil_mem_Cone : ([] : Str) ∈ Cone.sys.master := rfl

theorem MExpr_rooted : MExpr.RootedConst := ⟨nil_mem_Cone, trivial⟩

theorem M_eq_solution :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (MExpr.obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem MExpr MExpr_rooted

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

def gFix (T : GExpr) : Set Str := ⋃ n, gIter T n

theorem gFix_fixed (T : GExpr) (hT : T.RootedConst) : gFun T (gFix T) = gFix T :=
  gFun_iter_fixed T hT

theorem gFix_nil_mem (T : GExpr) : ([] : Str) ∈ gFix T :=
  Set.mem_iUnion.mpr ⟨0, rfl⟩

theorem gFix_nonempty (T : GExpr) : (gFix T).Nonempty := ⟨[], gFix_nil_mem T⟩

def gGen (T : GExpr) : ScottSys := singletonSys (gFix T) (gFix_nonempty T)

@[simp] theorem gGen_master (T : GExpr) : (gGen T).sys.master = gFix T := rfl

theorem gBase (T : GExpr) (hT : T.RootedConst) : (gGen T).sys ◁ (T.obj (gGen T)).sys := by
  have hmaster : (T.obj (gGen T)).sys.master = gFix T :=
    (gFun_eq_master T (gFix_nonempty T)).symm.trans (gFix_fixed T hT)
  refine ⟨hmaster.symm, ?_, ?_⟩
  · intro X hX
    have heq : X = (T.obj (gGen T)).sys.master := (hX : X = gFix T).trans hmaster.symm
    rw [heq]; exact (T.obj (gGen T)).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = gFix T
    rw [show X = gFix T from hX, show Y = gFix T from hY, Set.inter_self]

def gTower (T : GExpr) : ℕ → ScottSys
  | 0 => gGen T
  | n + 1 => T.obj (gTower T n)

@[simp] theorem gTower_zero (T : GExpr) : gTower T 0 = gGen T := rfl

@[simp] theorem gTower_succ (T : GExpr) (n : ℕ) : gTower T (n + 1) = T.obj (gTower T n) := rfl

theorem gChain (T : GExpr) (hT : T.RootedConst) :
    ∀ n, (gTower T n).sys ◁ (gTower T (n + 1)).sys
  | 0 => gBase T hT
  | n + 1 => T.obj_subsystem (gChain T hT n)

theorem gTower_le (T : GExpr) (hT : T.RootedConst) {n m : ℕ} (h : n ≤ m) :
    (gTower T n).sys ◁ (gTower T m).sys := by
  induction h with
  | refl => exact Subsystem.refl _
  | step _ ih => exact ih.trans (gChain T hT _)

theorem gTower_master (T : GExpr) (hT : T.RootedConst) :
    ∀ n, (gTower T n).sys.master = gFix T
  | 0 => rfl
  | n + 1 => ((gChain T hT n).master_eq).symm.trans (gTower_master T hT n)

def gColim (T : GExpr) (hT : T.RootedConst) : ScottSys where
  sys :=
    { mem := fun X => ∃ n, (gTower T n).sys.mem X
      master := gFix T
      master_nonempty := (gTower T 0).sys.master_nonempty
      master_mem := ⟨0, (gTower T 0).sys.master_mem⟩
      inter_mem := by
        rintro X Y Z ⟨n, hX⟩ ⟨m, hY⟩ ⟨p, hZ⟩ hsub
        set N := max n (max m p) with hN
        have hXN : (gTower T N).sys.mem X := (gTower_le T hT (le_max_left n _)).sub hX
        have hYN : (gTower T N).sys.mem Y :=
          (gTower_le T hT ((le_max_left m p).trans (le_max_right n _))).sub hY
        have hZN : (gTower T N).sys.mem Z :=
          (gTower_le T hT ((le_max_right m p).trans (le_max_right n _))).sub hZ
        exact ⟨N, (gTower T N).sys.inter_mem hXN hYN hZN hsub⟩
      sub_master := by
        rintro X ⟨n, hX⟩
        rw [← gTower_master T hT n]
        exact (gTower T n).sys.sub_master hX }
  ne := by rintro X ⟨n, hX⟩; exact (gTower T n).ne X hX

@[simp] theorem mem_gColim (T : GExpr) (hT : T.RootedConst) {X : Set Str} :
    (gColim T hT).sys.mem X ↔ ∃ n, (gTower T n).sys.mem X := Iff.rfl

@[simp] theorem gColim_master (T : GExpr) (hT : T.RootedConst) :
    (gColim T hT).sys.master = gFix T := rfl

def Texp (N : ScottSys) : GExpr :=
  .oplus (.const N) (.sum (.prod .var .var) (.prod .var .var))

theorem Texp_rooted {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) : (Texp N).RootedConst :=
  ⟨hN, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

def Exp (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) : ScottSys :=
  gColim (Texp N) (Texp_rooted hN)

theorem ScottSys.ext {A B : ScottSys} (h : A.sys = B.sys) : A = B := by
  cases A; cases B; cases h; rfl

instance : Category ScottSys where
  Hom A B := StrictMap A.sys B.sys
  id A := ⟨idMap A.sys, isStrict_idMap⟩
  comp f g := ⟨g.1.comp f.1, isStrict_comp g.2 f.2⟩
  id_comp f := Subtype.ext (comp_idMap f.1)
  comp_id f := Subtype.ext (idMap_comp f.1)
  assoc f g h := Subtype.ext (comp_assoc h.1 g.1 f.1).symm

theorem gTower_sub_colim (T : GExpr) (hT : T.RootedConst) (n : ℕ) :
    (gTower T n).sys ◁ (gColim T hT).sys where
  master_eq := by rw [gColim_master, gTower_master T hT]
  sub hX := ⟨n, hX⟩
  inter_closed := by
    rintro X Y hX hY ⟨m, hXY⟩
    have hN : (gTower T (max n m)).sys.mem (X ∩ Y) :=
      (gTower_le T hT (le_max_right n m)).sub hXY
    exact (gTower_le T hT (le_max_left n m)).inter_closed hX hY hN

theorem gColim_obj_sys_eq (T : GExpr) (hT : T.RootedConst) :
    (T.obj (gColim T hT)).sys = (gColim T hT).sys := by
  set ℱ : Set ScottSys := Set.range (gTower T) with hℱ
  have hne : ℱ.Nonempty := ⟨gTower T 0, 0, rfl⟩
  have hsub : ∀ D ∈ ℱ, D.sys ◁ (gColim T hT).sys := by
    rintro D ⟨n, rfl⟩; exact gTower_sub_colim T hT n
  have hdir : DirectedOn (fun a b => a.sys ◁ b.sys) ℱ := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    exact ⟨gTower T (max n m), ⟨max n m, rfl⟩,
      gTower_le T hT (le_max_left n m), gTower_le T hT (le_max_right n m)⟩
  have hU : ∀ X, (gColim T hT).sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X := by
    intro X; constructor
    · rintro ⟨n, hn⟩; exact ⟨gTower T n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨D, ⟨n, rfl⟩, hn⟩; exact ⟨n, hn⟩
  apply NeighborhoodSystem.ext
  · intro W
    rw [T.obj_continuous hdir hne hsub hU W]
    constructor
    · rintro ⟨D, ⟨n, rfl⟩, hn⟩

      exact ⟨n + 1, hn⟩
    · rintro ⟨n, hn⟩

      exact ⟨gTower T n, ⟨n, rfl⟩, (gChain T hT n).sub hn⟩
  ·
    have h := (T.obj_subsystem (gTower_sub_colim T hT 0)).master_eq
    rw [gColim_master]
    rw [show (T.obj (gTower T 0)) = gTower T 1 from rfl] at h
    rw [← h, gTower_master T hT]

theorem gColim_obj_eq (T : GExpr) (hT : T.RootedConst) : T.obj (gColim T hT) = gColim T hT :=
  ScottSys.ext (gColim_obj_sys_eq T hT)

theorem Exp_structure_eq (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    (Texp N).obj (Exp N hN) = Exp N hN :=
  gColim_obj_eq (Texp N) (Texp_rooted hN)

@[simp] theorem ScottSys.id_val (A : ScottSys) :
    ((𝟙 A) : StrictMap A.sys A.sys).1 = idMap A.sys := rfl

@[simp] theorem ScottSys.comp_val {A B C : ScottSys} (g : (B ⟶ C)) (f : (A ⟶ B)) :
    ((g ⊚ f : StrictMap A.sys C.sys)).1 = g.1.comp f.1 := rfl

def gFunctorMap (T : GExpr) {X Y : ScottSys} (f : StrictMap X.sys Y.sys) :
    StrictMap (T.obj X).sys (T.obj Y).sys :=
  ⟨T.map f.1, T.map_isStrict f.1 f.2⟩

abbrev gFunctor (T : GExpr) : Endofunctor ScottSys where
  obj := T.obj
  map := gFunctorMap T
  map_id X := Subtype.ext (T.map_id X)
  map_comp {_ _ _} g f :=
    Subtype.ext (T.map_comp (f : StrictMap _ _).1 (g : StrictMap _ _).2)

@[simp] theorem gFunctor_obj (T : GExpr) (X : ScottSys) : (gFunctor T).obj X = T.obj X := rfl

@[simp] theorem gFunctorMap_val (T : GExpr) {X Y : ScottSys} (f : StrictMap X.sys Y.sys) :
    (gFunctorMap T f).1 = T.map f.1 := rfl

abbrev TexpF (N : ScottSys) : Endofunctor ScottSys := gFunctor (Texp N)

def algStr (B : TAlgebra (TexpF N)) :
    ApproximableMap ((TexpF N).obj B.carrier).sys B.carrier.sys :=
  (B.str : StrictMap ((TexpF N).obj B.carrier).sys B.carrier.sys).1

theorem algStr_strict (B : TAlgebra (TexpF N)) : IsStrict (algStr B) :=
  (B.str : StrictMap ((TexpF N).obj B.carrier).sys B.carrier.sys).2

def isoOfObjEq {Obj : Type*} [Category Obj] {X Y : Obj} (h : X = Y) : Iso X Y := by
  cases h
  exact ⟨(𝟙 X), (𝟙 X), CategoryTheory.Category.id_comp _, CategoryTheory.Category.id_comp _⟩

def ExpIso (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    Iso ((TexpF N).obj (Exp N hN)) (Exp N hN) :=
  isoOfObjEq (Exp_structure_eq N hN)

abbrev ExpAlg (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) : TAlgebra (TexpF N) where
  carrier := Exp N hN
  str := (ExpIso N hN).hom

def expHom (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    ApproximableMap ((TexpF N).obj (Exp N hN)).sys (Exp N hN).sys :=
  ((ExpIso N hN).hom : StrictMap ((TexpF N).obj (Exp N hN)).sys (Exp N hN).sys).1

def expInv (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    ApproximableMap (Exp N hN).sys ((TexpF N).obj (Exp N hN)).sys :=
  ((ExpIso N hN).inv : StrictMap (Exp N hN).sys ((TexpF N).obj (Exp N hN)).sys).1

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

def descRel : ℕ → ApproximableMap (Exp N hN).sys B.carrier.sys
  | 0 => constMap (Exp N hN).sys B.carrier.sys.bot
  | n + 1 => (algStr B).comp (((Texp N).map (descRel n)).comp (expInv N hN))

@[simp] theorem descRel_succ (n : ℕ) :
    descRel hN B (n + 1) = (algStr B).comp (((Texp N).map (descRel hN B n)).comp (expInv N hN)) :=
  rfl

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

variable (B : TAlgebra (TexpF N))

theorem algHom_ext {A C : TAlgebra (TexpF N)} {g g' : AlgHom A C} (h : g.hom = g'.hom) : g = g' := by
  cases g; cases g'; cases h; rfl

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

theorem constBot_le {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (g : ApproximableMap V₀ V₁) : constMap V₀ V₁.bot ≤ g := by
  intro X Y hr
  obtain ⟨hX, hY⟩ := hr
  rw [NeighborhoodSystem.mem_bot] at hY
  subst hY
  exact g.mono g.master_rel (V₀.sub_master hX) subset_rfl hX V₁.master_mem

theorem descRel_le_succ : ∀ n, descRel hN B n ≤ descRel hN B (n + 1)
  | 0 => constBot_le _
  | n + 1 => by
      rw [descRel_succ, descRel_succ]
      exact comp_mono_gen le_rfl
        (comp_mono_gen ((Texp N).map_mono (descRel_le_succ n)) le_rfl)

theorem descRel_mono {i j : ℕ} (h : i ≤ j) : descRel hN B i ≤ descRel hN B j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (descRel_le_succ hN B _)

theorem descDir (i j : ℕ) : ∃ k, (∀ X Y, (descRel hN B i).rel X Y → (descRel hN B k).rel X Y) ∧
    (∀ X Y, (descRel hN B j).rel X Y → (descRel hN B k).rel X Y) :=
  ⟨max i j, descRel_mono hN B (le_max_left i j), descRel_mono hN B (le_max_right i j)⟩

theorem descDirLe (i j : ℕ) :
    ∃ k, descRel hN B i ≤ descRel hN B k ∧ descRel hN B j ≤ descRel hN B k :=
  ⟨max i j, descRel_mono hN B (le_max_left i j), descRel_mono hN B (le_max_right i j)⟩

def descMap : ApproximableMap (Exp N hN).sys B.carrier.sys :=
  iSupMap (descRel hN B) (descDir hN B)

theorem descMap_is_sup (A E : Set Str) :
    (descMap hN B).rel A E ↔ ∃ n, (descRel hN B n).rel A E := Iff.rfl

theorem descMap_fix :
    descMap hN B = (algStr B).comp (((Texp N).map (descMap hN B)).comp (expInv N hN)) := by
  have hmc : ∀ Y C, ((Texp N).map (descMap hN B)).rel Y C
      ↔ ∃ n, ((Texp N).map (descRel hN B n)).rel Y C :=
    fun Y C => (Texp N).map_continuous (descRel hN B) (descMap hN B) (descDirLe hN B)
      (descMap_is_sup hN B) Y C
  apply ApproximableMap.ext
  intro A E
  rw [comp_rel]
  constructor
  · rintro ⟨n, hn⟩
    have hn1 : (descRel hN B (n + 1)).rel A E := descRel_le_succ hN B n A E hn
    rw [descRel_succ, comp_rel] at hn1
    obtain ⟨C, hAC, hCE⟩ := hn1
    rw [comp_rel] at hAC
    obtain ⟨Y, hAY, hYC⟩ := hAC
    exact ⟨C, ⟨Y, hAY, (hmc Y C).mpr ⟨n, hYC⟩⟩, hCE⟩
  · rintro ⟨C, hAC, hCE⟩
    rw [comp_rel] at hAC
    obtain ⟨Y, hAY, hYC⟩ := hAC
    obtain ⟨n, hn⟩ := (hmc Y C).mp hYC
    refine ⟨n + 1, ?_⟩
    rw [descRel_succ, comp_rel]
    exact ⟨C, by rw [comp_rel]; exact ⟨Y, hAY, hn⟩, hCE⟩

theorem descMap_rel {A E : Set Str} :
    (descMap hN B).rel A E ↔ ∃ n, (descRel hN B n).rel A E := Iff.rfl

end Existence

theorem expInv_comp_expHom (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    (expInv N hN).comp (expHom N hN) = idMap ((TexpF N).obj (Exp N hN)).sys := by
  have h := congrArg (Subtype.val) (ExpIso N hN).hom_inv_id
  exact h

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

theorem descComm :
    (descMap hN B).comp (expHom N hN) = (algStr B).comp ((Texp N).map (descMap hN B)) := by
  calc (descMap hN B).comp (expHom N hN)
      = ((algStr B).comp (((Texp N).map (descMap hN B)).comp (expInv N hN))).comp (expHom N hN) := by
        rw [← descMap_fix]
    _ = (algStr B).comp ((((Texp N).map (descMap hN B)).comp (expInv N hN)).comp (expHom N hN)) := by
        rw [comp_assoc]
    _ = (algStr B).comp (((Texp N).map (descMap hN B)).comp ((expInv N hN).comp (expHom N hN))) := by
        rw [comp_assoc]
    _ = (algStr B).comp (((Texp N).map (descMap hN B)).comp (idMap _)) := by
        rw [expInv_comp_expHom]
    _ = (algStr B).comp ((Texp N).map (descMap hN B)) := by rw [comp_idMap]

end Existence

theorem expInv_strict (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) : IsStrict (expInv N hN) :=
  ((ExpIso N hN).inv : StrictMap (Exp N hN).sys ((TexpF N).obj (Exp N hN)).sys).2

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

theorem descRel_isStrict : ∀ n, IsStrict (descRel hN B n)
  | 0 => isStrict_constBot
  | n + 1 => by
      rw [descRel_succ]
      exact isStrict_comp (algStr_strict B)
        (isStrict_comp ((Texp N).map_isStrict _ (descRel_isStrict n)) (expInv_strict N hN))

theorem descMap_isStrict : IsStrict (descMap hN B) := by
  rintro Y ⟨n, hn⟩
  exact descRel_isStrict hN B n hn

def descAlgHom : AlgHom (ExpAlg N hN) B where
  hom := ⟨descMap hN B, descMap_isStrict hN B⟩
  comm := by
    apply Subtype.ext
    show (descMap hN B).comp (expHom N hN) = (algStr B).comp ((Texp N).map (descMap hN B))
    exact descComm hN B

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

theorem expSub (n : ℕ) : (gTower (Texp N) n).sys ◁ (Exp N hN).sys :=
  gTower_sub_colim (Texp N) (Texp_rooted hN) n

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

theorem Subsystem.inj_isStrict {α : Type*} {D E : NeighborhoodSystem α} (h : D ◁ E) :
    IsStrict h.inj := by
  intro Y hrel
  rw [Subsystem.inj_rel] at hrel
  obtain ⟨_, hYE, hsub⟩ := hrel
  exact Set.Subset.antisymm (E.sub_master hYE) (by rw [← h.master_eq]; exact hsub)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

theorem isoOfObjEq_hom_rel {X Y : ScottSys} (e : X = Y) {A E : Set Str} :
    ((isoOfObjEq e).hom).1.rel A E ↔ X.sys.mem A ∧ Y.sys.mem E ∧ A ⊆ E := by
  cases e; exact idMap_rel

theorem expHom_rel {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) {A E : Set Str} :
    (expHom N hN).rel A E ↔
      ((Texp N).obj (Exp N hN)).sys.mem A ∧ (Exp N hN).sys.mem E ∧ A ⊆ E :=
  isoOfObjEq_hom_rel (Exp_structure_eq N hN)

theorem isoOfObjEq_inv_rel {X Y : ScottSys} (e : X = Y) {A E : Set Str} :
    ((isoOfObjEq e).inv).1.rel A E ↔ Y.sys.mem A ∧ X.sys.mem E ∧ A ⊆ E := by
  cases e; exact idMap_rel

theorem expInv_rel {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) {A E : Set Str} :
    (expInv N hN).rel A E ↔
      (Exp N hN).sys.mem A ∧ ((Texp N).obj (Exp N hN)).sys.mem E ∧ A ⊆ E :=
  isoOfObjEq_inv_rel (Exp_structure_eq N hN)

theorem oplusMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    oplusMapTok h0.inj h1.inj = (oplusTok_subsystem h0 h1).inj := by
  have hsubM : ∀ {W : Set Str}, (A₀.oplus A₁).sys.mem W → W ⊆ sumTokMaster B₀.sys B₁.sys := by
    rintro W (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
    · exact (show sumTokMaster A₀.sys A₁.sys = sumTokMaster B₀.sys B₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact embF_subset_sumTokMaster (h0.sub hX)
    · exact embT_subset_sumTokMaster (h1.sub hY)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXs⟩, hXne, hX'ne, rfl, rfl⟩ |
      ⟨Y, Y', ⟨hY, hY', hYs⟩, hYne, hY'ne, rfl, rfl⟩)
    · exact ⟨hW, (B₀.oplus B₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩), Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩),
        embBit_subset.mpr hXs⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩), Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩),
        embBit_subset.mpr hYs⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, hXne, hX'ne, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, hYne, hY'ne, rfl, rfl⟩)

theorem oplusMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    oplusMapTok h0.proj h1.proj = (oplusTok_subsystem h0 h1).proj := by
  have hsubM : ∀ {W : Set Str}, (B₀.oplus B₁).sys.mem W → W ⊆ sumTokMaster A₀.sys A₁.sys := by
    rintro W (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
    · exact (show sumTokMaster B₀.sys B₁.sys = sumTokMaster A₀.sys A₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact (embBit_subset.mpr (by rw [h0.master_eq]; exact B₀.sys.sub_master hX)).trans
        (embF_subset_sumTokMaster A₀.sys.master_mem)
    · exact (embBit_subset.mpr (by rw [h1.master_eq]; exact B₁.sys.sub_master hY)).trans
        (embT_subset_sumTokMaster A₁.sys.master_mem)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXs⟩, hXne, hX'ne, rfl, rfl⟩ |
      ⟨Y, Y', ⟨hY, hY', hYs⟩, hYne, hY'ne, rfl, rfl⟩)
    · exact ⟨hW, (A₀.oplus A₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩), Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩),
        embBit_subset.mpr hXs⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩), Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩),
        embBit_subset.mpr hYs⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, hXne, hX'ne, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, hYne, hY'ne, rfl, rfl⟩)

theorem otimesMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    otimesMapTok h0.inj h1.inj = (otimesTok_subsystem h0 h1).inj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ |
      ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩)
    · refine ⟨hW, (B₀.otimes B₁).sys.master_mem, ?_⟩
      rcases hW with rfl | ⟨P, Q, hP, hQ, hPne, hQne, rfl⟩
      · exact (show prodTokNbhd A₀.sys.master A₁.sys.master
            = prodTokNbhd B₀.sys.master B₁.sys.master by rw [h0.master_eq, h1.master_eq]).subset
      · exact prodTokNbhd_subset_iff.mpr ⟨B₀.sys.sub_master (h0.sub hP),
          B₁.sys.sub_master (h1.sub hQ)⟩
    · exact ⟨Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩, Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩,
        prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · obtain ⟨hsX, _⟩ := prodTokNbhd_subset_iff.mp hsub
        exact absurd (Set.Subset.antisymm (B₀.sys.sub_master hX')
          (by rw [← h0.master_eq]; exact hsX)) hX'ne
      · obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
        exact Or.inr ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩,
          hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩

theorem otimesMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    otimesMapTok h0.proj h1.proj = (otimesTok_subsystem h0 h1).proj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ |
      ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩)
    · refine ⟨hW, (A₀.otimes A₁).sys.master_mem, ?_⟩
      rcases hW with rfl | ⟨P, Q, hP, hQ, hPne, hQne, rfl⟩
      · exact (show prodTokNbhd B₀.sys.master B₁.sys.master
            = prodTokNbhd A₀.sys.master A₁.sys.master by rw [h0.master_eq, h1.master_eq]).subset
      · exact prodTokNbhd_subset_iff.mpr ⟨by rw [h0.master_eq]; exact B₀.sys.sub_master hP,
          by rw [h1.master_eq]; exact B₁.sys.sub_master hQ⟩
    · exact ⟨Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩, Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩,
        prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · obtain ⟨hsX, _⟩ := prodTokNbhd_subset_iff.mp hsub
        exact absurd (Set.Subset.antisymm (A₀.sys.sub_master hX')
          (by rw [h0.master_eq]; exact hsX)) hX'ne
      · obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
        exact Or.inr ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩,
          hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩

theorem prodMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    prodMapTok h0.inj h1.inj = (prodTok_subsystem h0 h1).inj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩
    exact ⟨prodTok_mem_prodTokNbhd hX hY, prodTok_mem_prodTokNbhd hX' hY',
      prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨⟨X, Y, hX, hY, rfl⟩, ⟨X', Y', hX', hY', rfl⟩, hsub⟩
    obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩

theorem prodMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    prodMapTok h0.proj h1.proj = (prodTok_subsystem h0 h1).proj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩
    exact ⟨prodTok_mem_prodTokNbhd hX hY, prodTok_mem_prodTokNbhd hX' hY',
      prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨⟨X, Y, hX, hY, rfl⟩, ⟨X', Y', hX', hY', rfl⟩, hsub⟩
    obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

def rho (n : ℕ) : ApproximableMap (Exp N hN).sys (Exp N hN).sys :=
  (expSub hN n).inj.comp (expSub hN n).proj

theorem rho_rel (n : ℕ) {A E : Set Str} :
    (rho hN n).rel A E ↔ (Exp N hN).sys.mem A ∧ (Exp N hN).sys.mem E ∧
      ∃ z, (gTower (Texp N) n).sys.mem z ∧ A ⊆ z ∧ z ⊆ E := by
  unfold rho
  rw [comp_rel]
  constructor
  · rintro ⟨z, hproj, hinj⟩
    rw [Subsystem.proj_rel] at hproj
    rw [Subsystem.inj_rel] at hinj
    obtain ⟨hcA, hTz, hAz⟩ := hproj
    obtain ⟨_, hcE, hzE⟩ := hinj
    exact ⟨hcA, hcE, z, hTz, hAz, hzE⟩
  · rintro ⟨hcA, hcE, z, hTz, hAz, hzE⟩
    exact ⟨z, by rw [Subsystem.proj_rel]; exact ⟨hcA, hTz, hAz⟩,
      by rw [Subsystem.inj_rel]; exact ⟨hTz, hcE, hzE⟩⟩

theorem rho_mono {n m : ℕ} (h : n ≤ m) {A E : Set Str} (hr : (rho hN n).rel A E) :
    (rho hN m).rel A E := by
  rw [rho_rel] at hr ⊢
  obtain ⟨hcA, hcE, z, hTz, hAz, hzE⟩ := hr
  exact ⟨hcA, hcE, z, (gTower_le (Texp N) (Texp_rooted hN) h).sub hTz, hAz, hzE⟩

def iSupRho : ApproximableMap (Exp N hN).sys (Exp N hN).sys :=
  iSupMap (rho hN) (fun i j => ⟨max i j,
    fun _ _ h => rho_mono hN (le_max_left i j) h,
    fun _ _ h => rho_mono hN (le_max_right i j) h⟩)

theorem iSupRho_eq_id : iSupRho hN = idMap (Exp N hN).sys := by
  apply ApproximableMap.ext
  intro A E
  rw [idMap_rel]
  constructor
  · rintro ⟨n, hr⟩
    rw [rho_rel] at hr
    obtain ⟨hcA, hcE, z, _, hAz, hzE⟩ := hr
    exact ⟨hcA, hcE, hAz.trans hzE⟩
  · rintro ⟨hcA, hcE, hAE⟩
    obtain ⟨n, hA⟩ := hcA
    exact ⟨n, (rho_rel hN n).mpr ⟨⟨n, hA⟩, hcE, A, hA, subset_rfl, hAE⟩⟩

theorem rho_zero_rel {A E : Set Str} :
    (rho hN 0).rel A E ↔ (Exp N hN).sys.mem A ∧ E = (Exp N hN).sys.master := by
  rw [rho_rel]
  constructor
  · rintro ⟨hcA, hcE, z, hz, _, hzE⟩
    have hzm : z = (Exp N hN).sys.master :=
      (hz : z = gFix (Texp N)).trans (gColim_master (Texp N) (Texp_rooted hN)).symm
    subst hzm
    exact ⟨hcA, Set.Subset.antisymm ((Exp N hN).sys.sub_master hcE) hzE⟩
  · rintro ⟨hcA, rfl⟩
    exact ⟨hcA, (Exp N hN).sys.master_mem, (Exp N hN).sys.master,
      gColim_master (Texp N) (Texp_rooted hN), (Exp N hN).sys.sub_master hcA, subset_rfl⟩

end Uniqueness

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

variable (B : TAlgebra (TexpF N))

theorem gcomp_rho_zero (g : AlgHom (ExpAlg N hN) B) :
    g.hom.1.comp (rho hN 0) = descRel hN B 0 := by
  apply ApproximableMap.ext
  intro A Z
  rw [comp_rel]
  constructor
  · rintro ⟨E, hrho, hg⟩
    rw [rho_zero_rel] at hrho
    obtain ⟨hcA, rfl⟩ := hrho
    have hZ : Z = B.carrier.sys.master := g.hom.2 hg
    exact ⟨hcA, by rw [NeighborhoodSystem.mem_bot]; exact hZ⟩
  · rintro ⟨hcA, hZ⟩
    rw [NeighborhoodSystem.mem_bot] at hZ
    subst hZ
    exact ⟨(Exp N hN).sys.master, (rho_zero_rel hN).mpr ⟨hcA, rfl⟩, g.hom.1.master_rel⟩

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

theorem Subsystem.self_inj {α : Type*} {D : NeighborhoodSystem α} (h : D ◁ D) :
    h.inj = idMap D := by
  apply ApproximableMap.ext
  intro X Y
  rw [Subsystem.inj_rel, idMap_rel]

theorem Subsystem.self_proj {α : Type*} {D : NeighborhoodSystem α} (h : D ◁ D) :
    h.proj = idMap D := by
  apply ApproximableMap.ext
  intro X Y
  rw [Subsystem.proj_rel, idMap_rel]

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

theorem sumMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    sumMapTok h0.inj h1.inj = (sumTok_subsystem h0 h1).inj := by
  have hsubM : ∀ {W : Set Str}, (A₀.sum A₁).sys.mem W → W ⊆ sumTokMaster B₀.sys B₁.sys := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact (show sumTokMaster A₀.sys A₁.sys = sumTokMaster B₀.sys B₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact embF_subset_sumTokMaster (h0.sub hX)
    · exact embT_subset_sumTokMaster (h1.sub hY)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXsub⟩, rfl, rfl⟩ | ⟨Y, Y', ⟨hY, hY', hYsub⟩, rfl, rfl⟩)
    · exact ⟨hW, (B₀.sum B₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨X', hX', rfl⟩), embBit_subset.mpr hXsub⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨Y', hY', rfl⟩), embBit_subset.mpr hYsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, rfl, rfl⟩)

theorem GExpr.map_inj : (T : GExpr) → {X Y : ScottSys} → (h : X.sys ◁ Y.sys) →
    T.map h.inj = (T.obj_subsystem h).inj
  | .const D, _, _, _ => (Subsystem.self_inj (Subsystem.refl D.sys)).symm
  | .var, _, _, _ => rfl
  | .sum a b, _, _, h => by
      show sumMapTok (a.map h.inj) (b.map h.inj)
          = (sumTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, sumMapTok_inj]
  | .prod a b, _, _, h => by
      show prodMapTok (a.map h.inj) (b.map h.inj)
          = (prodTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, prodMapTok_inj]
  | .oplus a b, _, _, h => by
      show oplusMapTok (a.map h.inj) (b.map h.inj)
          = (oplusTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, oplusMapTok_inj]
  | .otimes a b, _, _, h => by
      show otimesMapTok (a.map h.inj) (b.map h.inj)
          = (otimesTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, otimesMapTok_inj]

theorem sumMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    sumMapTok h0.proj h1.proj = (sumTok_subsystem h0 h1).proj := by
  have hsubM : ∀ {W : Set Str}, (B₀.sum B₁).sys.mem W → W ⊆ sumTokMaster A₀.sys A₁.sys := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact (show sumTokMaster B₀.sys B₁.sys = sumTokMaster A₀.sys A₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact (embBit_subset.mpr (by rw [h0.master_eq]; exact B₀.sys.sub_master hX)).trans
        (embF_subset_sumTokMaster A₀.sys.master_mem)
    · exact (embBit_subset.mpr (by rw [h1.master_eq]; exact B₁.sys.sub_master hY)).trans
        (embT_subset_sumTokMaster A₁.sys.master_mem)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXsub⟩, rfl, rfl⟩ | ⟨Y, Y', ⟨hY, hY', hYsub⟩, rfl, rfl⟩)
    · exact ⟨hW, (A₀.sum A₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨X', hX', rfl⟩), embBit_subset.mpr hXsub⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨Y', hY', rfl⟩), embBit_subset.mpr hYsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, rfl, rfl⟩)

theorem GExpr.map_proj : (T : GExpr) → {X Y : ScottSys} → (h : X.sys ◁ Y.sys) →
    T.map h.proj = (T.obj_subsystem h).proj
  | .const D, _, _, _ => (Subsystem.self_proj (Subsystem.refl D.sys)).symm
  | .var, _, _, _ => rfl
  | .sum a b, _, _, h => by
      show sumMapTok (a.map h.proj) (b.map h.proj)
          = (sumTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, sumMapTok_proj]
  | .prod a b, _, _, h => by
      show prodMapTok (a.map h.proj) (b.map h.proj)
          = (prodTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, prodMapTok_proj]
  | .oplus a b, _, _, h => by
      show oplusMapTok (a.map h.proj) (b.map h.proj)
          = (oplusTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, oplusMapTok_proj]
  | .otimes a b, _, _, h => by
      show otimesMapTok (a.map h.proj) (b.map h.proj)
          = (otimesTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, otimesMapTok_proj]

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

theorem map_rho_eq (n : ℕ) :
    (Texp N).map (rho hN n)
      = ((Texp N).obj_subsystem (expSub hN n)).inj.comp
        ((Texp N).obj_subsystem (expSub hN n)).proj := by
  unfold rho
  rw [(Texp N).map_comp (expSub hN n).proj (Subsystem.inj_isStrict (expSub hN n)),
      (Texp N).map_inj, (Texp N).map_proj]

theorem key_rho (n : ℕ) :
    rho hN (n + 1)
      = (expHom N hN).comp (((Texp N).map (rho hN n)).comp (expInv N hN)) := by
  have hsyseq : ((Texp N).obj (Exp N hN)).sys = (Exp N hN).sys :=
    gColim_obj_sys_eq (Texp N) (Texp_rooted hN)
  apply ApproximableMap.ext
  intro A E
  rw [map_rho_eq]
  simp only [comp_rel, rho_rel, expInv_rel, expHom_rel, Subsystem.proj_rel,
    Subsystem.inj_rel, hsyseq]
  constructor
  · rintro ⟨hcA, hcE, z, hTz, hAz, hzE⟩
    exact ⟨E, ⟨A, ⟨hcA, hcA, subset_rfl⟩, z, ⟨hcA, hTz, hAz⟩, hTz, hcE, hzE⟩,
      hcE, hcE, subset_rfl⟩
  · rintro ⟨Y, ⟨C, ⟨hcA, _, hAC⟩, z, ⟨_, hTz, hCz⟩, _, _, hzY⟩, _, hcE, hYE⟩
    exact ⟨hcA, hcE, z, hTz, hAC.trans hCz, hzY.trans hYE⟩

end Uniqueness

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

variable (B : TAlgebra (TexpF N))

theorem gcomp_rho_succ (g : AlgHom (ExpAlg N hN) B) (n : ℕ) :
    g.hom.1.comp (rho hN (n + 1))
      = (algStr B).comp (((Texp N).map (g.hom.1.comp (rho hN n))).comp (expInv N hN)) := by
  have hcomm : (g.hom.1).comp (expHom N hN) = (algStr B).comp ((Texp N).map g.hom.1) :=
    congrArg Subtype.val g.comm
  calc g.hom.1.comp (rho hN (n + 1))
      = g.hom.1.comp ((expHom N hN).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN))) := by rw [key_rho]
    _ = (g.hom.1.comp (expHom N hN)).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN)) :=
        (comp_assoc _ _ _).symm
    _ = ((algStr B).comp ((Texp N).map g.hom.1)).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN)) :=
        congrArg (fun m => m.comp (((Texp N).map (rho hN n)).comp (expInv N hN))) hcomm
    _ = (algStr B).comp (((Texp N).map g.hom.1).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN))) := comp_assoc _ _ _
    _ = (algStr B).comp ((((Texp N).map g.hom.1).comp ((Texp N).map (rho hN n))).comp
          (expInv N hN)) :=
        congrArg ((algStr B).comp ·)
          (comp_assoc ((Texp N).map g.hom.1) ((Texp N).map (rho hN n)) (expInv N hN)).symm
    _ = (algStr B).comp (((Texp N).map (g.hom.1.comp (rho hN n))).comp (expInv N hN)) :=
        congrArg (fun m => (algStr B).comp (m.comp (expInv N hN)))
          ((Texp N).map_comp (rho hN n) g.hom.2).symm

theorem gcomp_rho_eq (g : AlgHom (ExpAlg N hN) B) :
    ∀ n, g.hom.1.comp (rho hN n) = descRel hN B n
  | 0 => gcomp_rho_zero hN B g
  | n + 1 => by rw [gcomp_rho_succ hN B g n, gcomp_rho_eq g n, ← descRel_succ]

theorem descMap_eq_algHom (g : AlgHom (ExpAlg N hN) B) : g.hom.1 = descMap hN B := by
  have hcomp : g.hom.1.comp (iSupRho hN) = descMap hN B := by
    apply ApproximableMap.ext
    intro A E
    rw [comp_rel, descMap_rel]
    constructor
    · rintro ⟨Y, ⟨n, hrho⟩, hg⟩
      refine ⟨n, ?_⟩
      rw [← gcomp_rho_eq hN B g n, comp_rel]
      exact ⟨Y, hrho, hg⟩
    · rintro ⟨n, hn⟩
      rw [← gcomp_rho_eq hN B g n, comp_rel] at hn
      obtain ⟨Y, hrho, hg⟩ := hn
      exact ⟨Y, ⟨n, hrho⟩, hg⟩
  calc g.hom.1 = g.hom.1.comp (iSupRho hN) := by
        rw [iSupRho_eq_id hN]; exact (comp_idMap g.hom.1).symm
    _ = descMap hN B := hcomp

end Uniqueness

end Exercise619
end
end DomainTheory.NeighbourhoodSystems
end
