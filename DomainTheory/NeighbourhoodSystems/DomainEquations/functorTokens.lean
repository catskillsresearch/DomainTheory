module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumProdTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example_6_2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subdomain
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.smashProduct
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap BitDom SeqEqB
open DomainTheory.NeighbourhoodSystems.FunctorTokens
open DomainTheory.NeighbourhoodSystems.SeqEqB DomainTheory.NeighbourhoodSystems.BitDom
open DomainTheory.NeighbourhoodSystems.SmashProduct

namespace FunctorTokens
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.FunctorTokens
open DomainTheory.NeighbourhoodSystems.SeqEqB DomainTheory.NeighbourhoodSystems.BitDom
open DomainTheory.NeighbourhoodSystems.SmashProduct

structure ScottSys where

  sys : NeighborhoodSystem Str

  ne : ∀ X, sys.mem X → X.Nonempty

end FunctorTokens
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.FunctorTokens
open DomainTheory.NeighbourhoodSystems.SeqEqB DomainTheory.NeighbourhoodSystems.BitDom
open DomainTheory.NeighbourhoodSystems.SmashProduct

section
namespace FunctorTokens

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

inductive FExpr where
  | const : ScottSys → FExpr
  | var : FExpr
  | sum : FExpr → FExpr → FExpr
  | prod : FExpr → FExpr → FExpr

theorem embBit_not_subset_cross {b b' : Bool} (h : b ≠ b') {X Y : Set Str} (hX : X.Nonempty)
    (hsub : embBit b X ⊆ embBit b' Y) : False := by
  obtain ⟨t, ht⟩ := hX
  obtain ⟨w', he, -⟩ := hsub ⟨t, rfl, ht⟩
  simp only [List.cons.injEq] at he
  exact h he.1

end FunctorTokens
end

namespace FunctorTokens

def ScottSys.prod (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨prodTok A₀.sys A₁.sys, prodTok_nonempty⟩

end FunctorTokens

section
namespace FunctorTokens

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

def prodMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.prod A₁).sys (B₀.prod B₁).sys where
  rel W W' := ∃ X Y X' Y', f₀.rel X X' ∧ f₁.rel Y Y' ∧
    W = prodTokNbhd X Y ∧ W' = prodTokNbhd X' Y'
  rel_dom := by
    rintro W W' ⟨X, Y, X', Y', h0, h1, rfl, -⟩
    exact prodTok_mem_prodTokNbhd (f₀.rel_dom h0) (f₁.rel_dom h1)
  rel_cod := by
    rintro W W' ⟨X, Y, X', Y', h0, h1, -, rfl⟩
    exact prodTok_mem_prodTokNbhd (f₀.rel_cod h0) (f₁.rel_cod h1)
  master_rel :=
    ⟨A₀.sys.master, A₁.sys.master, B₀.sys.master, B₁.sys.master,
      f₀.master_rel, f₁.master_rel, rfl, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨X, Y, X', Y', h0, h1, rfl, rfl⟩ ⟨X₂, Y₂, X'₂, Y'₂, h0₂, h1₂, hWeq, rfl⟩
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective hWeq
    exact ⟨X, Y, X' ∩ X'₂, Y' ∩ Y'₂, f₀.inter_right h0 h0₂, f₁.inter_right h1 h1₂, rfl,
      prodTokNbhd_inter X' X'₂ Y' Y'₂⟩
  mono := by
    rintro W W'' Z Z' ⟨X, Y, X', Y', h0, h1, rfl, rfl⟩ hWW hZZ' hW'' hZ'
    obtain ⟨X₂, Y₂, hX₂, hY₂, rfl⟩ := hW''
    obtain ⟨X'₃, Y'₃, hX'₃, hY'₃, rfl⟩ := hZ'
    obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp hWW
    obtain ⟨hsX', hsY'⟩ := prodTokNbhd_subset_iff.mp hZZ'
    exact ⟨X₂, Y₂, X'₃, Y'₃, f₀.mono h0 hsX hsX' hX₂ hX'₃, f₁.mono h1 hsY hsY' hY₂ hY'₃, rfl, rfl⟩

def singletonSys (Γ : Set Str) (h : Γ.Nonempty) : ScottSys where
  sys :=
    { mem := fun X => X = Γ
      master := Γ
      master_nonempty := h
      master_mem := rfl
      inter_mem := by
        intro X Y Z hX hY _ _
        show X ∩ Y = Γ
        rw [hX, hY, Set.inter_self]
      sub_master := by intro X hX; rw [show X = Γ from hX] }
  ne := by intro X hX; rw [show X = Γ from hX]; exact h

end FunctorTokens
end

namespace FunctorTokens

def ScottSys.sum (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨sumTok A₀.sys A₁.sys A₀.ne A₁.ne, sumTok_nonempty⟩

end FunctorTokens

section
namespace FunctorTokens

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

def FExpr.RootedConst : FExpr → Prop
  | .const C => ([] : Str) ∈ C.sys.master
  | .var => True
  | .sum a b => a.RootedConst ∧ b.RootedConst
  | .prod a b => a.RootedConst ∧ b.RootedConst

def mFun : FExpr → Set Str → Set Str
  | .const C, _ => C.sys.master
  | .var, Γ => Γ
  | .sum T₀ T₁, Γ => insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))
  | .prod T₀ T₁, Γ => insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))

def mIter (T : FExpr) : ℕ → Set Str
  | 0 => {([] : Str)}
  | n + 1 => mFun T (mIter T n)

def FExpr.obj : FExpr → ScottSys → ScottSys
  | .const D, _ => D
  | .var, X => X
  | .sum T₀ T₁, X => (T₀.obj X).sum (T₁.obj X)
  | .prod T₀ T₁, X => (T₀.obj X).prod (T₁.obj X)

def sumMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.sum A₁).sys (B₀.sum B₁).sys where
  rel W W' :=
    ((sumTok A₀.sys A₁.sys A₀.ne A₁.ne).mem W ∧ W' = sumTokMaster B₀.sys B₁.sys) ∨
    (∃ X X', f₀.rel X X' ∧ W = embBit false X ∧ W' = embBit false X') ∨
    (∃ Y Y', f₁.rel Y Y' ∧ W = embBit true Y ∧ W' = embBit true Y')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, X', hrel, rfl, -⟩ | ⟨Y, Y', hrel, rfl, -⟩)
    · exact hW
    · exact Or.inr (Or.inl ⟨X, f₀.rel_dom hrel, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, f₁.rel_dom hrel, rfl⟩)
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, X', hrel, -, rfl⟩ | ⟨Y, Y', hrel, -, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X', f₀.rel_cod hrel, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y', f₁.rel_cod hrel, rfl⟩)
  master_rel := Or.inl ⟨(A₀.sum A₁).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩ | ⟨Y, Y', hrel, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, X', hrel, hWeq, rfl⟩ | ⟨Y, Y', hrel, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · exact Or.inr (Or.inl ⟨X, X', hrel, hWeq, by rw [sumTokMaster_inter_embF (f₀.rel_cod hrel)]⟩)
      · exact Or.inr (Or.inr ⟨Y, Y', hrel, hWeq, by rw [sumTokMaster_inter_embT (f₁.rel_cod hrel)]⟩)
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, hWeq, rfl⟩
      · refine Or.inr (Or.inl ⟨X, X', hrel, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embF (f₀.rel_cod hrel)]
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inl ⟨X, X' ∩ X'₂, f₀.inter_right hrel hrel₂, rfl, embBit_inter false X' X'₂⟩)
      · exact absurd hWeq (embBit_ne (by decide) (A₀.ne X (f₀.rel_dom hrel)))
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, hWeq, rfl⟩
      · refine Or.inr (Or.inr ⟨Y, Y', hrel, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embT (f₁.rel_cod hrel)]
      · exact absurd hWeq (embBit_ne (by decide) (A₁.ne Y (f₁.rel_dom hrel)))
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inr ⟨Y, Y' ∩ Y'₂, f₁.inter_right hrel hrel₂, rfl, embBit_inter true Y' Y'₂⟩)
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hW'' hZ'
    rcases h with ⟨-, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩ | ⟨Y, Y', hrel, rfl, rfl⟩
    ·
      exact Or.inl ⟨hW'', Set.Subset.antisymm ((B₀.sum B₁).sys.sub_master hZ') hZZ'⟩
    ·
      rcases hZ' with rfl | ⟨X₃, hX₃, rfl⟩ | ⟨Y₃, hY₃, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · rcases hW'' with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact Or.inr (Or.inl ⟨X₂, X₃,
            f₀.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hX₂ hX₃, rfl, rfl⟩)
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₁.ne Y₂ hY₂) hsub)
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₀.ne X' (f₀.rel_cod hrel)) hsub)
    ·
      rcases hZ' with rfl | ⟨X₃, hX₃, rfl⟩ | ⟨Y₃, hY₃, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₁.ne Y' (f₁.rel_cod hrel)) hsub)
      · rcases hW'' with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₀.ne X₂ hX₂) hsub)
        · exact Or.inr (Or.inr ⟨Y₂, Y₃,
            f₁.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hY₂ hY₃, rfl, rfl⟩)

def FExpr.map : (T : FExpr) → {X Y : ScottSys} → ApproximableMap X.sys Y.sys →
    ApproximableMap (T.obj X).sys (T.obj Y).sys
  | .const D, _, _, _ => idMap D.sys
  | .var, _, _, f => f
  | .sum T₀ T₁, _, _, f => sumMapTok (T₀.map f) (T₁.map f)
  | .prod T₀ T₁, _, _, f => prodMapTok (T₀.map f) (T₁.map f)

def ScottSys.tok (D : ScottSys) : Set Str := D.sys.master

theorem mFun_eq_master : (T : FExpr) → {Γ : Set Str} → (h : Γ.Nonempty) →
    mFun T Γ = (T.obj (singletonSys Γ h)).sys.master
  | .const _, _, _ => rfl
  | .var, _, _ => rfl
  | .sum T₀ T₁, Γ, h => by
      show insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))
        = insert ([] : Str) (embBit false ((T₀.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((T₁.obj (singletonSys Γ h)).sys.master))
      rw [mFun_eq_master T₀ h, mFun_eq_master T₁ h]
  | .prod T₀ T₁, Γ, h => by
      show insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))
        = insert ([] : Str) (embBit false ((T₀.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((T₁.obj (singletonSys Γ h)).sys.master))
      rw [mFun_eq_master T₀ h, mFun_eq_master T₁ h]

theorem insertTag_mono {p q p' q' : Set Str} (hp : p ⊆ p') (hq : q ⊆ q') :
    insert ([] : Str) (embBit false p ∪ embBit true q)
      ⊆ insert ([] : Str) (embBit false p' ∪ embBit true q') := by
  rintro w (rfl | hw | hw)
  · exact Or.inl rfl
  · obtain ⟨w', rfl, hw'⟩ := hw
    exact Or.inr (Or.inl ⟨w', rfl, hp hw'⟩)
  · obtain ⟨w', rfl, hw'⟩ := hw
    exact Or.inr (Or.inr ⟨w', rfl, hq hw'⟩)

theorem mFun_mono (T : FExpr) {Γ Γ' : Set Str} (h : Γ ⊆ Γ') : mFun T Γ ⊆ mFun T Γ' := by
  induction T with
  | const C => exact subset_rfl
  | var => exact h
  | sum T₀ T₁ ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | prod T₀ T₁ ih₀ ih₁ => exact insertTag_mono ih₀ ih₁

theorem insertTag_continuous {ℱ : Set (Set Str)} {U : Set Str} (hne : ℱ.Nonempty)
    {p q : Set Str → Set Str}
    (hp : ∀ w, w ∈ p U ↔ ∃ Γ ∈ ℱ, w ∈ p Γ)
    (hq : ∀ w, w ∈ q U ↔ ∃ Γ ∈ ℱ, w ∈ q Γ) (w : Str) :
    (w ∈ insert ([] : Str) (embBit false (p U) ∪ embBit true (q U)))
      ↔ ∃ Γ ∈ ℱ, w ∈ insert ([] : Str) (embBit false (p Γ) ∪ embBit true (q Γ)) := by
  simp only [Set.mem_insert_iff, Set.mem_union]
  constructor
  · rintro (rfl | hw | hw)
    · obtain ⟨Γ, hΓ⟩ := hne; exact ⟨Γ, hΓ, Or.inl rfl⟩
    · obtain ⟨w', rfl, hw'⟩ := hw
      obtain ⟨Γ, hΓ, hpΓ⟩ := (hp w').mp hw'
      exact ⟨Γ, hΓ, Or.inr (Or.inl ⟨w', rfl, hpΓ⟩)⟩
    · obtain ⟨w', rfl, hw'⟩ := hw
      obtain ⟨Γ, hΓ, hqΓ⟩ := (hq w').mp hw'
      exact ⟨Γ, hΓ, Or.inr (Or.inr ⟨w', rfl, hqΓ⟩)⟩
  · rintro ⟨Γ, hΓ, (rfl | hw | hw)⟩
    · exact Or.inl rfl
    · obtain ⟨w', rfl, hw'⟩ := hw
      exact Or.inr (Or.inl ⟨w', rfl, (hp w').mpr ⟨Γ, hΓ, hw'⟩⟩)
    · obtain ⟨w', rfl, hw'⟩ := hw
      exact Or.inr (Or.inr ⟨w', rfl, (hq w').mpr ⟨Γ, hΓ, hw'⟩⟩)

theorem mFun_continuous (T : FExpr) {ℱ : Set (Set Str)} {U : Set Str}
    (_hdir : DirectedOn (· ⊆ ·) ℱ) (hne : ℱ.Nonempty)
    (hU : ∀ w, w ∈ U ↔ ∃ Γ ∈ ℱ, w ∈ Γ) :
    ∀ w, w ∈ mFun T U ↔ ∃ Γ ∈ ℱ, w ∈ mFun T Γ := by
  induction T with
  | const C =>
      intro w
      exact ⟨fun hw => let ⟨Γ, hΓ⟩ := hne; ⟨Γ, hΓ, hw⟩, fun ⟨_, _, hw⟩ => hw⟩
  | var => intro w; exact hU w
  | sum T₀ T₁ ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | prod T₀ T₁ ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w

theorem mFun_nil_mem : ∀ (T : FExpr), T.RootedConst → {Γ : Set Str} →
    ([] : Str) ∈ Γ → ([] : Str) ∈ mFun T Γ
  | .const _, hC, _, _ => hC
  | .var, _, _, hΓ => hΓ
  | .sum _ _, _, _, _ => Set.mem_insert _ _
  | .prod _ _, _, _, _ => Set.mem_insert _ _

theorem nil_mem_mIter (T : FExpr) (hT : T.RootedConst) : ∀ n, ([] : Str) ∈ mIter T n
  | 0 => rfl
  | n + 1 => mFun_nil_mem T hT (nil_mem_mIter T hT n)

theorem mIter_mono_step (T : FExpr) (hT : T.RootedConst) :
    ∀ n, mIter T n ⊆ mIter T (n + 1)
  | 0 => by
      intro w hw
      have hw' : w = [] := hw
      subst hw'
      exact mFun_nil_mem T hT rfl
  | n + 1 => mFun_mono T (mIter_mono_step T hT n)

theorem mIter_mono (T : FExpr) (hT : T.RootedConst) {m n : ℕ} (hmn : m ≤ n) :
    mIter T m ⊆ mIter T n := by
  induction hmn with
  | refl => exact subset_rfl
  | step _ ih => intro x hx; exact mIter_mono_step T hT _ (ih hx)

theorem mFun_iter_fixed (T : FExpr) (hT : T.RootedConst) :
    mFun T (⋃ n, mIter T n) = ⋃ n, mIter T n := by
  have hstep := mIter_mono_step T hT
  have hne : (Set.range (mIter T)).Nonempty := ⟨mIter T 0, 0, rfl⟩
  have hdir : DirectedOn (· ⊆ ·) (Set.range (mIter T)) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ⟨mIter T (max i j), ⟨max i j, rfl⟩,
      mIter_mono T hT (le_max_left i j), mIter_mono T hT (le_max_right i j)⟩
  have hU : ∀ v, v ∈ (⋃ n, mIter T n) ↔ ∃ S ∈ Set.range (mIter T), v ∈ S := by
    intro v
    constructor
    · intro hv; rw [Set.mem_iUnion] at hv; obtain ⟨n, hn⟩ := hv
      exact ⟨mIter T n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨S, ⟨n, rfl⟩, hv⟩; exact Set.mem_iUnion.mpr ⟨n, hv⟩
  apply Set.ext; intro w
  rw [mFun_continuous T hdir hne hU w]
  constructor
  · rintro ⟨S, ⟨n, rfl⟩, hwS⟩; exact Set.mem_iUnion.mpr ⟨n + 1, hwS⟩
  · intro hw
    rw [Set.mem_iUnion] at hw; obtain ⟨n, hn⟩ := hw
    exact ⟨mIter T n, ⟨n, rfl⟩, hstep n hn⟩

theorem exists_tok_fixedPoint (T : FExpr) (hT : T.RootedConst) :
    ∃ Γ : Set Str, ([] : Str) ∈ Γ ∧ mFun T Γ = Γ :=
  ⟨⋃ n, mIter T n, Set.mem_iUnion.mpr ⟨0, nil_mem_mIter T hT 0⟩, mFun_iter_fixed T hT⟩

theorem exists_singleton_subsystem (T : FExpr) (hT : T.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (T.obj (singletonSys Γ h)).sys := by
  obtain ⟨Γ, hnil, hfix⟩ := exists_tok_fixedPoint T hT
  have hne : Γ.Nonempty := ⟨[], hnil⟩

  have hmaster : (T.obj (singletonSys Γ hne)).sys.master = Γ :=
    (mFun_eq_master T hne).symm.trans hfix
  refine ⟨Γ, hne, ?_, ?_, ?_⟩
  ·
    exact hmaster.symm
  ·
    intro X hX
    have heq : X = (T.obj (singletonSys Γ hne)).sys.master := (hX : X = Γ).trans hmaster.symm
    rw [heq]
    exact (T.obj (singletonSys Γ hne)).sys.master_mem
  ·
    intro X Y hX hY _
    show X ∩ Y = Γ
    rw [show X = Γ from hX, show Y = Γ from hY, Set.inter_self]

theorem prodMapTok_comp (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys)
    (g₀ : ApproximableMap B₀.sys C₀.sys) (g₁ : ApproximableMap B₁.sys C₁.sys) :
    prodMapTok (g₀.comp f₀) (g₁.comp f₁) = (prodMapTok g₀ g₁).comp (prodMapTok f₀ f₁) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro ⟨X, Y, X'', Y'', ⟨X', hf0, hg0⟩, ⟨Y', hf1, hg1⟩, rfl, rfl⟩
    exact ⟨prodTokNbhd X' Y', ⟨X, Y, X', Y', hf0, hf1, rfl, rfl⟩,
      ⟨X', Y', X'', Y'', hg0, hg1, rfl, rfl⟩⟩
  · rintro ⟨W', ⟨X, Y, X', Y', hf0, hf1, rfl, rfl⟩, ⟨X₂, Y₂, X'', Y'', hg0, hg1, hWeq, rfl⟩⟩
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective hWeq
    exact ⟨X, Y, X'', Y'', ⟨X', hf0, hg0⟩, ⟨Y', hf1, hg1⟩, rfl, rfl⟩

theorem prodMapTok_id :
    prodMapTok (idMap A₀.sys) (idMap A₁.sys) = idMap (A₀.prod A₁).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro ⟨X, Y, X', Y', ⟨hX, hX', hsX⟩, ⟨hY, hY', hsY⟩, rfl, rfl⟩
    exact ⟨prodTok_mem_prodTokNbhd hX hY, prodTok_mem_prodTokNbhd hX' hY',
      prodTokNbhd_subset_iff.mpr ⟨hsX, hsY⟩⟩
  · rintro ⟨⟨X, Y, hX, hY, rfl⟩, ⟨X', Y', hX', hY', rfl⟩, hsub⟩
    obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X, Y, X', Y', ⟨hX, hX', hsX⟩, ⟨hY, hY', hsY⟩, rfl, rfl⟩

theorem prodMapTok_isStrict {f₀ : ApproximableMap A₀.sys B₀.sys}
    {f₁ : ApproximableMap A₁.sys B₁.sys} (hf₀ : IsStrict f₀) (hf₁ : IsStrict f₁) :
    IsStrict (prodMapTok f₀ f₁) := by
  rintro Y ⟨X, Y0, X', Y', h0, h1, hWeq, rfl⟩
  obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective hWeq
  rw [hf₀ h0, hf₁ h1]
  rfl

theorem prodMapTok_mono {f₀ f₀' : ApproximableMap A₀.sys B₀.sys}
    {f₁ f₁' : ApproximableMap A₁.sys B₁.sys} (h0 : f₀ ≤ f₀') (h1 : f₁ ≤ f₁') :
    prodMapTok f₀ f₁ ≤ prodMapTok f₀' f₁' := by
  rw [ApproximableMap.le_iff]
  rintro W W' ⟨X, Y, X', Y', hr0, hr1, rfl, rfl⟩
  exact ⟨X, Y, X', Y', h0 X X' hr0, h1 Y Y' hr1, rfl, rfl⟩

theorem prodTok_subsystem (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    (A₀.prod A₁).sys ◁ (B₀.prod B₁).sys := by
  have heqm : prodTokNbhd A₀.sys.master A₁.sys.master
      = prodTokNbhd B₀.sys.master B₁.sys.master := by rw [h0.master_eq, h1.master_eq]
  refine ⟨heqm, ?_, ?_⟩
  · rintro W ⟨X, Y, hX, hY, rfl⟩
    exact ⟨X, Y, h0.sub hX, h1.sub hY, rfl⟩
  · rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ hInt
    rw [prodTokNbhd_inter] at hInt ⊢
    obtain ⟨X'', Y'', hX'', hY'', heq⟩ := hInt
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
    exact ⟨X ∩ X', Y ∩ Y', h0.inter_closed hX hX' hX'', h1.inter_closed hY hY' hY'', rfl⟩

theorem sumMapTok_comp (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys)
    (g₀ : ApproximableMap B₀.sys C₀.sys) (g₁ : ApproximableMap B₁.sys C₁.sys) :
    sumMapTok (g₀.comp f₀) (g₁.comp f₁) = (sumMapTok g₀ g₁).comp (sumMapTok f₀ f₁) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩ | ⟨Y, Y'', ⟨Y', hf, hg⟩, rfl, rfl⟩)
    · exact ⟨sumTokMaster B₀.sys B₁.sys, Or.inl ⟨hW, rfl⟩,
        Or.inl ⟨(B₀.sum B₁).sys.master_mem, rfl⟩⟩
    · exact ⟨embBit false X', Or.inr (Or.inl ⟨X, X', hf, rfl, rfl⟩),
        Or.inr (Or.inl ⟨X', X'', hg, rfl, rfl⟩)⟩
    · exact ⟨embBit true Y', Or.inr (Or.inr ⟨Y, Y', hf, rfl, rfl⟩),
        Or.inr (Or.inr ⟨Y', Y'', hg, rfl, rfl⟩)⟩
  · rintro ⟨W', hWW', hW'W''⟩
    rcases hWW' with ⟨hW, rfl⟩ | ⟨X, X', hf, rfl, rfl⟩ | ⟨Y, Y', hf, rfl, rfl⟩
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X, X', -, heq, -⟩ | ⟨Y, Y', -, heq, -⟩
      · exact Or.inl ⟨hW, rfl⟩
      · exact absurd (heq ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd (heq ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, heq, rfl⟩ | ⟨Y₂, Y'', hg, heq, -⟩
      · exact Or.inl ⟨Or.inr (Or.inl ⟨X, f₀.rel_dom hf, rfl⟩), rfl⟩
      · obtain rfl := embBit_injective heq
        exact Or.inr (Or.inl ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩)
      · exact absurd heq (embBit_ne (by decide) (B₀.ne X' (f₀.rel_cod hf)))
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, heq, -⟩ | ⟨Y₂, Y'', hg, heq, rfl⟩
      · exact Or.inl ⟨Or.inr (Or.inr ⟨Y, f₁.rel_dom hf, rfl⟩), rfl⟩
      · exact absurd heq (embBit_ne (by decide) (B₁.ne Y' (f₁.rel_cod hf)))
      · obtain rfl := embBit_injective heq
        exact Or.inr (Or.inr ⟨Y, Y'', ⟨Y', hf, hg⟩, rfl, rfl⟩)

theorem FExpr.map_comp : (T : FExpr) → {X Y Z : ScottSys} → (f : ApproximableMap X.sys Y.sys) →
    (g : ApproximableMap Y.sys Z.sys) → T.map (g.comp f) = (T.map g).comp (T.map f)
  | .const D, _, _, _, _, _ => (idMap_comp (idMap D.sys)).symm
  | .var, _, _, _, _, _ => rfl
  | .sum T₀ T₁, _, _, _, f, g => by
      show sumMapTok (T₀.map (g.comp f)) (T₁.map (g.comp f))
          = (sumMapTok (T₀.map g) (T₁.map g)).comp (sumMapTok (T₀.map f) (T₁.map f))
      rw [T₀.map_comp f g, T₁.map_comp f g, sumMapTok_comp]
  | .prod T₀ T₁, _, _, _, f, g => by
      show prodMapTok (T₀.map (g.comp f)) (T₁.map (g.comp f))
          = (prodMapTok (T₀.map g) (T₁.map g)).comp (prodMapTok (T₀.map f) (T₁.map f))
      rw [T₀.map_comp f g, T₁.map_comp f g, prodMapTok_comp]

theorem sumMapTok_id :
    sumMapTok (idMap A₀.sys) (idMap A₁.sys) = idMap (A₀.sum A₁).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hsub⟩, rfl, rfl⟩ | ⟨Y, Y', ⟨hY, hY', hsub⟩, rfl, rfl⟩)
    · exact ⟨hW, (A₀.sum A₁).sys.master_mem, (A₀.sum A₁).sys.sub_master hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨X', hX', rfl⟩), embBit_subset.mpr hsub⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨Y', hY', rfl⟩), embBit_subset.mpr hsub⟩
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

theorem FExpr.map_id : (T : FExpr) → (X : ScottSys) → T.map (idMap X.sys) = idMap (T.obj X).sys
  | .const D, _ => rfl
  | .var, _ => rfl
  | .sum T₀ T₁, X => by
      show sumMapTok (T₀.map (idMap X.sys)) (T₁.map (idMap X.sys))
          = idMap ((T₀.obj X).sum (T₁.obj X)).sys
      rw [T₀.map_id X, T₁.map_id X, sumMapTok_id]
  | .prod T₀ T₁, X => by
      show prodMapTok (T₀.map (idMap X.sys)) (T₁.map (idMap X.sys))
          = idMap ((T₀.obj X).prod (T₁.obj X)).sys
      rw [T₀.map_id X, T₁.map_id X, prodMapTok_id]

theorem sumMapTok_isStrict (f₀ : ApproximableMap A₀.sys B₀.sys)
    (f₁ : ApproximableMap A₁.sys B₁.sys) : IsStrict (sumMapTok f₀ f₁) := by
  rintro Y (⟨-, rfl⟩ | ⟨X, X', -, heq, -⟩ | ⟨Y0, Y', -, heq, -⟩)
  · rfl
  · have heq' : sumTokMaster A₀.sys A₁.sys = embBit false X := heq
    exact absurd (heq' ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · have heq' : sumTokMaster A₀.sys A₁.sys = embBit true Y0 := heq
    exact absurd (heq' ▸ nil_mem_sumTokMaster) nil_not_mem_embBit

theorem FExpr.map_isStrict : (T : FExpr) → {X Y : ScottSys} → (f : ApproximableMap X.sys Y.sys) →
    IsStrict f → IsStrict (T.map f)
  | .const _, _, _, _, _ => isStrict_idMap
  | .var, _, _, _, hf => hf
  | .sum T₀ T₁, _, _, f, _ => sumMapTok_isStrict (T₀.map f) (T₁.map f)
  | .prod T₀ T₁, _, _, f, hf =>
      prodMapTok_isStrict (T₀.map_isStrict f hf) (T₁.map_isStrict f hf)

theorem sumMapTok_mono {f₀ f₀' : ApproximableMap A₀.sys B₀.sys}
    {f₁ f₁' : ApproximableMap A₁.sys B₁.sys} (h0 : f₀ ≤ f₀') (h1 : f₁ ≤ f₁') :
    sumMapTok f₀ f₁ ≤ sumMapTok f₀' f₁' := by
  rw [ApproximableMap.le_iff]
  rintro W W' (⟨hW, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩ | ⟨Y, Y', hrel, rfl, rfl⟩)
  · exact Or.inl ⟨hW, rfl⟩
  · exact Or.inr (Or.inl ⟨X, X', h0 X X' hrel, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨Y, Y', h1 Y Y' hrel, rfl, rfl⟩)

theorem FExpr.map_mono : (T : FExpr) → {X Y : ScottSys} → {f f' : ApproximableMap X.sys Y.sys} →
    f ≤ f' → T.map f ≤ T.map f'
  | .const _, _, _, _, _, _ => le_rfl
  | .var, _, _, _, _, h => h
  | .sum T₀ T₁, _, _, _, _, h => sumMapTok_mono (T₀.map_mono h) (T₁.map_mono h)
  | .prod T₀ T₁, _, _, _, _, h => prodMapTok_mono (T₀.map_mono h) (T₁.map_mono h)

theorem FExpr.map_continuous_mp : (T : FExpr) → {I : Type} → {X Y : ScottSys} →
    {g : I → ApproximableMap X.sys Y.sys} → {f : ApproximableMap X.sys Y.sys} →
    [Nonempty I] → (∀ i j, ∃ k, g i ≤ g k ∧ g j ≤ g k) →
    (∀ A B, f.rel A B ↔ ∃ i, (g i).rel A B) →
    {A B : Set Str} → (T.map f).rel A B → ∃ i, (T.map (g i)).rel A B
  | .const _, _, _, _, _, _, _, _, _, _, _, hrel => by
      obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, hrel⟩
  | .var, _, _, _, _, _, _, _, hf, A, B, hrel => (hf A B).mp hrel
  | .sum T₀ T₁, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      rcases hrel with ⟨hA, rfl⟩ | ⟨P, P', hr, rfl, rfl⟩ | ⟨Q, Q', hr, rfl, rfl⟩
      · obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, Or.inl ⟨hA, rfl⟩⟩
      · obtain ⟨i, hi⟩ := T₀.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inl ⟨P, P', hi, rfl, rfl⟩)⟩
      · obtain ⟨i, hi⟩ := T₁.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inr ⟨Q, Q', hi, rfl, rfl⟩)⟩
  | .prod T₀ T₁, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      obtain ⟨P, Q, P', Q', hr0, hr1, rfl, rfl⟩ := hrel
      obtain ⟨i, hi⟩ := T₀.map_continuous_mp hdir hf hr0
      obtain ⟨j, hj⟩ := T₁.map_continuous_mp hdir hf hr1
      obtain ⟨k, hik, hjk⟩ := hdir i j
      exact ⟨k, P, Q, P', Q', (T₀.map_mono hik) P P' hi, (T₁.map_mono hjk) Q Q' hj, rfl, rfl⟩

theorem FExpr.map_continuous (T : FExpr) {I : Type} [Nonempty I] {X Y : ScottSys}
    (g : I → ApproximableMap X.sys Y.sys) (f : ApproximableMap X.sys Y.sys)
    (hdir : ∀ i j, ∃ k, g i ≤ g k ∧ g j ≤ g k)
    (hf : ∀ A B, f.rel A B ↔ ∃ i, (g i).rel A B) (A B : Set Str) :
    (T.map f).rel A B ↔ ∃ i, (T.map (g i)).rel A B := by
  refine ⟨T.map_continuous_mp hdir hf, ?_⟩
  rintro ⟨i, hi⟩
  have hgif : g i ≤ f := by
    rw [ApproximableMap.le_iff]; intro A' B' h; exact (hf A' B').mpr ⟨i, h⟩
  exact (T.map_mono hgif) A B hi

theorem sumTok_subsystem (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    (A₀.sum A₁).sys ◁ (B₀.sum B₁).sys := by
  have heqm : sumTokMaster A₀.sys A₁.sys = sumTokMaster B₀.sys B₁.sys := by
    unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]
  refine ⟨heqm, ?_, ?_⟩
  · rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact Or.inl heqm
    · exact Or.inr (Or.inl ⟨X, h0.sub hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, h1.sub hY, rfl⟩)
  · rintro W W' (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) (rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [sumTokMaster_inter_embF hX']; exact Or.inr (Or.inl ⟨X', hX', rfl⟩)
    · rw [sumTokMaster_inter_embT hY']; exact Or.inr (Or.inr ⟨Y', hY', rfl⟩)
    · rw [Set.inter_comm, sumTokMaster_inter_embF hX]; exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · rw [embBit_inter] at hInt ⊢
      exact Or.inr (Or.inl ⟨X ∩ X',
        h0.inter_closed hX hX' (sumTok_mem_embF_inv (h₀ := B₀.ne) (h₁ := B₁.ne) hInt), rfl⟩)
    · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hInt
      exact absurd ((B₀.sum B₁).ne _ hInt) Set.not_nonempty_empty
    · rw [Set.inter_comm, sumTokMaster_inter_embT hY]; exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
    · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hInt
      exact absurd ((B₀.sum B₁).ne _ hInt) Set.not_nonempty_empty
    · rw [embBit_inter] at hInt ⊢
      exact Or.inr (Or.inr ⟨Y ∩ Y',
        h1.inter_closed hY hY' (sumTok_mem_embT_inv (h₀ := B₀.ne) (h₁ := B₁.ne) hInt), rfl⟩)

theorem FExpr.obj_subsystem : (T : FExpr) → {X Y : ScottSys} → X.sys ◁ Y.sys →
    (T.obj X).sys ◁ (T.obj Y).sys
  | .const D, _, _, _ => Subsystem.refl D.sys
  | .var, _, _, h => h
  | .sum T₀ T₁, _, _, h => sumTok_subsystem (T₀.obj_subsystem h) (T₁.obj_subsystem h)
  | .prod T₀ T₁, _, _, h => prodTok_subsystem (T₀.obj_subsystem h) (T₁.obj_subsystem h)

theorem FExpr.obj_continuous_mp : (T : FExpr) → {ℱ : Set ScottSys} → {U : ScottSys} →
    DirectedOn (fun a b => a.sys ◁ b.sys) ℱ → ℱ.Nonempty →
    (∀ D ∈ ℱ, D.sys ◁ U.sys) → (∀ X, U.sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X) →
    {W : Set Str} → (T.obj U).sys.mem W → ∃ D ∈ ℱ, (T.obj D).sys.mem W
  | .const _, _, _, _, hne, _, _, _, hmem => by
      obtain ⟨D, hD⟩ := hne; exact ⟨D, hD, hmem⟩
  | .var, _, _, _, _, _, hU, W, hmem => (hU W).mp hmem
  | .sum T₀ T₁, _, _, hdir, hne, hsub, hU, _, hmem => by
      rcases hmem with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · obtain ⟨D, hD⟩ := hne
        exact ⟨D, hD, Or.inl ((FExpr.sum T₀ T₁).obj_subsystem (hsub D hD)).master_eq.symm⟩
      · obtain ⟨D, hD, hXD⟩ := T₀.obj_continuous_mp hdir hne hsub hU hX
        exact ⟨D, hD, Or.inr (Or.inl ⟨X, hXD, rfl⟩)⟩
      · obtain ⟨D, hD, hYD⟩ := T₁.obj_continuous_mp hdir hne hsub hU hY
        exact ⟨D, hD, Or.inr (Or.inr ⟨Y, hYD, rfl⟩)⟩
  | .prod T₀ T₁, _, _, hdir, hne, hsub, hU, _, hmem => by
      obtain ⟨X, Y, hX, hY, rfl⟩ := hmem
      obtain ⟨D₁, hD₁, hXD⟩ := T₀.obj_continuous_mp hdir hne hsub hU hX
      obtain ⟨D₂, hD₂, hYD⟩ := T₁.obj_continuous_mp hdir hne hsub hU hY
      obtain ⟨D₃, hD₃, hr1, hr2⟩ := hdir D₁ hD₁ D₂ hD₂
      exact ⟨D₃, hD₃, X, Y, (T₀.obj_subsystem hr1).sub hXD, (T₁.obj_subsystem hr2).sub hYD, rfl⟩

theorem FExpr.obj_continuous (T : FExpr) {ℱ : Set ScottSys} {U : ScottSys}
    (hdir : DirectedOn (fun a b => a.sys ◁ b.sys) ℱ) (hne : ℱ.Nonempty)
    (hsub : ∀ D ∈ ℱ, D.sys ◁ U.sys) (hU : ∀ X, U.sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X)
    (W : Set Str) : (T.obj U).sys.mem W ↔ ∃ D ∈ ℱ, (T.obj D).sys.mem W := by
  refine ⟨T.obj_continuous_mp hdir hne hsub hU, ?_⟩
  rintro ⟨D, hD, hmem⟩
  exact (T.obj_subsystem (hsub D hD)).sub hmem

end FunctorTokens
end

section
namespace FunctorTokens

variable {D₀ D₁ : NeighborhoodSystem Str}
variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}
variable {A₀ A₁ B₀ B₁ : ScottSys}
variable {C₀ C₁ : ScottSys}

inductive GExpr where
  | const : ScottSys → GExpr
  | var : GExpr
  | sum : GExpr → GExpr → GExpr
  | prod : GExpr → GExpr → GExpr
  | oplus : GExpr → GExpr → GExpr
  | otimes : GExpr → GExpr → GExpr

end FunctorTokens
end

section
namespace FunctorTokens

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem inter_ne_of_ne_left {X X' Δ : Set Str} (hX : X ⊆ Δ) (hne : X ≠ Δ) : X ∩ X' ≠ Δ := by
  intro h
  exact hne (Set.Subset.antisymm hX (by rw [← h]; exact Set.inter_subset_left))

end FunctorTokens
end

section
namespace FunctorTokens

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

def GExpr.naryOp (op : GExpr → GExpr → GExpr) (a : GExpr) : List GExpr → GExpr
  | [] => a
  | b :: l => op a (GExpr.naryOp op b l)

def GExpr.naryProd : GExpr → List GExpr → GExpr := GExpr.naryOp GExpr.prod

def GExpr.narySum : GExpr → List GExpr → GExpr := GExpr.naryOp GExpr.sum

end FunctorTokens
end

end DomainTheory.NeighbourhoodSystems
end
