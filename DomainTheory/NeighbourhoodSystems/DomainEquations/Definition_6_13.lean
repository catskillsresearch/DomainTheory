module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem_6_9

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
universe w

def MonotoneOnDomains (T : Endofunctor DomainObj.{w}) : Prop :=
  ∀ {α : Type w} {D E : NeighborhoodSystem α} (h : D ◁ E), MonotoneAt T h

def targetFam (T : Endofunctor DomainObj.{w}) (hmono : MonotoneOnDomains T)
    {α : Type w} {D E : NeighborhoodSystem α} (h : D ◁ E) :
    Set (Set (T.obj ⟨α, E⟩).carrier) :=
  {Y | (T.obj ⟨α, D⟩).sys.mem ((hmono h).carrier_eq ▸ Y)}

def ContinuousOnDomains (T : Endofunctor DomainObj.{w}) : Prop :=
  ∃ hmono : MonotoneOnDomains T,
    ∀ {α : Type w} {E : NeighborhoodSystem α}
      (ℱ : Set (NeighborhoodSystem α)) (hℱ : ∀ ⦃D⦄, D ∈ ℱ → D ◁ E)
      (_hne : ℱ.Nonempty) (_hdir : DirectedOn (· ◁ ·) ℱ)
      {U : NeighborhoodSystem α} (hUE : U ◁ E)
      (_hU : ∀ X, U.mem X ↔ ∃ D ∈ ℱ, D.mem X),
      targetFam T hmono hUE = ⋃ D, ⋃ hD : D ∈ ℱ, targetFam T hmono (hℱ hD)

end

section

theorem monotoneOnDomains_id : MonotoneOnDomains (idEndofunctor DomainObj.{w}) := by
  intro α D E h
  exact ⟨rfl, h, HEq.rfl, HEq.rfl⟩
end

section

theorem continuousOnDomains_id : ContinuousOnDomains (idEndofunctor DomainObj.{w}) := by
  refine ⟨monotoneOnDomains_id, ?_⟩
  intro α E ℱ hℱ _hne _hdir U hUE hU
  apply Set.ext
  intro Y
  simp only [targetFam, Set.mem_iUnion, exists_prop]
  exact hU Y
end

namespace Exercise619
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

section

structure ScottSys where

  sys : NeighborhoodSystem Str

  ne : ∀ X, sys.mem X → X.Nonempty
end

end Exercise619
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

section
namespace Exercise619

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

end Exercise619
end

section
namespace Exercise619

def ScottSys.prod (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨prodTok A₀.sys A₁.sys, prodTok_nonempty⟩

end Exercise619
end

section
namespace Exercise619

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

end Exercise619
end

section
namespace Exercise619

def ScottSys.sum (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨sumTok A₀.sys A₁.sys A₀.ne A₁.ne, sumTok_nonempty⟩

end Exercise619
end

section
namespace Exercise619

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

end Exercise619
end
end DomainTheory.NeighbourhoodSystems
end
