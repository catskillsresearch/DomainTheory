/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda

/-!
# Scott 1976, §4 — retracts and data types

Definitions of composition, retracts, `⊑`, `∘→`, `⊗`, `⊕`, and
Theorems 4.1–4.6.
-/

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.5).** Composition `u ∘ v = λx. u(v(x))`. -/
def comp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))

theorem comp_app (u v x : Pomega) :
    funOf (comp u v) x = funOf u (funOf v x) :=
  beta (theorem_1_3 (funOf_isScottContinuous u) (funOf_isScottContinuous v)) x

/-- **Scott 1976, §4, Definition.** `a` is a retract iff `a = a ∘ a`. -/
def IsRetract (a : Pomega) : Prop :=
  a = comp a a

/-- The range / fixed-point set of a map. -/
def Fixpoints (f : Pomega → Pomega) : Set Pomega :=
  {x | f x = x}

/-- Directedness of fixed points under subset, without a lattice instance. -/
def IsDirectedSubset {f : Pomega → Pomega} (s : Set (Fixpoints f)) : Prop :=
  s.Nonempty ∧
    ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
      ∃ z ∈ s, (x : Pomega) ⊆ z ∧ (y : Pomega) ⊆ z

/-- Compactness of a fixed point under subset, without a lattice instance. -/
def IsCompactSubset {f : Pomega → Pomega} (x : Fixpoints f) : Prop :=
  ∀ s : Set (Fixpoints f),
    IsDirectedSubset s →
      (x : Pomega) ⊆ ⋃₀ (Subtype.val '' s) →
      ∃ z ∈ s, (x : Pomega) ⊆ z

/-- **Scott 1976, §4, Definition.** `u : a` means `u = a(u)`. -/
def typed (u a : Pomega) : Prop :=
  u = funOf a u

/-- **Scott 1976, (4.1).** The function-space retract `fun = λu λx. u(x)`. -/
def funRetract : Pomega :=
  graph (fun u => graph (fun x => funOf u x))

/-- **Scott 1976, (4.8).** Function space of retracts `a ∘→ b = λu. b ∘ u ∘ a`. -/
def arrowR (a b : Pomega) : Pomega :=
  graph (fun u => comp b (comp u a))

/-- **Scott 1976, (4.14)–(4.15).** Projections of a pair-as-function. -/
def fstC : Pomega := graph (fun u => funOf u (ofNat 0))
def sndC : Pomega := graph (fun u => funOf u (ofNat 1))

/-- **Scott 1976, (2.21) / (4.2).** Pairing as a distributive sequence. -/
def pairSeq (x y : Pomega) : Pomega := seq2 x y

/-- **Scott 1976, (4.9).** Product of retracts `a ⊗ b = λu. ⟨a(u₀), b(u₁)⟩`. -/
def tensorR (a b : Pomega) : Pomega :=
  graph (fun u =>
    pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))))

/-- **Scott 1976, (4.10), modified.** The displayed equation writes the
ordinary McCarthy conditional `⊃`. Lean uses the doubly strict
conditional `⊐` of (4.4), as in `bool` (4.3), which (4.8)–(4.10)
generalize. Mixed tags therefore map to `⊤` rather than the union of
the two injections; that is required for `⊕` to be a retract
(Theorem 4.5). This is not a symbol-for-symbol transcription of the
displayed (4.10). -/
def plusR (a b : Pomega) : Pomega :=
  graph (fun u =>
    dcondSet (funOf u (ofNat 0))
      (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
      (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))))

/-- **Scott 1976, §4, Definition.** `a ⊑ b` iff `a = a ∘ b = b ∘ a`. -/
def retractLe (a b : Pomega) : Prop :=
  a = comp a b ∧ a = comp b a

theorem retractLe_refl {a : Pomega} (ha : IsRetract a) : retractLe a a :=
  ⟨ha, ha⟩

theorem retractLe_trans {a b c : Pomega}
    (hab : retractLe a b) (hbc : retractLe b c) :
    a = comp a c ∧ a = comp c a := by
  rcases hab with ⟨hab₁, hab₂⟩
  rcases hbc with ⟨hbc₁, hbc₂⟩
  constructor
  · -- `a ∘ c = (a ∘ b) ∘ c = a ∘ (b ∘ c) = a ∘ b = a`
    apply Eq.trans hab₁
    apply Eq.symm
    calc
      comp a c = graph (fun x => funOf a (funOf c x)) := rfl
      _ = graph (fun x => funOf (comp a b) (funOf c x)) := by simp [← hab₁]
      _ = graph (fun x => funOf a (funOf b (funOf c x))) := by simp [comp_app]
      _ = graph (fun x => funOf a (funOf (comp b c) x)) := by simp [comp_app]
      _ = graph (fun x => funOf a (funOf b x)) := by simp [← hbc₁]
      _ = comp a b := rfl
  · -- `c ∘ a = c ∘ (b ∘ a) = (c ∘ b) ∘ a = b ∘ a = a`
    apply Eq.trans hab₂
    apply Eq.symm
    calc
      comp c a = graph (fun x => funOf c (funOf a x)) := rfl
      _ = graph (fun x => funOf c (funOf (comp b a) x)) := by simp [← hab₂]
      _ = graph (fun x => funOf c (funOf b (funOf a x))) := by simp [comp_app]
      _ = graph (fun x => funOf (comp c b) (funOf a x)) := by simp [comp_app]
      _ = graph (fun x => funOf b (funOf a x)) := by
        -- `c ∘ b = b` is `hbc₂`? `retractLe b c` is `b = b ∘ c` and `b = c ∘ b`
        simp [← hbc₂]
      _ = comp b a := rfl

/-- Directed iterates of `f` starting from `x` (Scott's sup construction). -/
def iterateFrom (f : Pomega → Pomega) (x : Pomega) : ℕ → Pomega
  | 0 => x
  | n + 1 => f (iterateFrom f x n)

/-- Least upper bound of fixed points above `x`: `⋃_n fⁿ(x)`. -/
def lfpAbove (f : Pomega → Pomega) (x : Pomega) : Pomega :=
  ⋃ n, iterateFrom f x n

/-- Greatest postfixed point of `z ↦ f z ∩ b` (Knaster–Tarski inf below `b`). -/
def gfpBelow (f : Pomega → Pomega) (b : Pomega) : Pomega :=
  ⋃₀ {x | x ⊆ f x ∩ b}

/-- The identity combinator `I = λu. u`, the largest retract. -/
def Icomb : Pomega := graph (fun x => x)

theorem iterateFrom_mono {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {x : Pomega} (hx : x ⊆ f x) :
    ∀ n, iterateFrom f x n ⊆ iterateFrom f x (n + 1)
  | 0 => hx
  | n + 1 => isScottContinuous_monotone hf (iterateFrom_mono hf hx n)

theorem sUnion_Fixpoints_le_image {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {A : Set Pomega} (hA : A ⊆ Fixpoints f) :
    ⋃₀ A ⊆ f (⋃₀ A) := by
  intro k hk
  obtain ⟨x, hxA, hkx⟩ := Set.mem_sUnion.mp hk
  have hx : f x = x := hA hxA
  have : k ∈ f x := by rwa [hx]
  exact isScottContinuous_monotone hf (Set.subset_sUnion_of_mem hxA) this

theorem lfpAbove_fixed {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {x : Pomega} (hx : x ⊆ f x) : f (lfpAbove f x) = lfpAbove f x := by
  have hchain := chain_lemma hf (iterateFrom f x) (iterateFrom_mono hf hx)
  unfold lfpAbove
  rw [hchain]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n + 1, hkn⟩
  · intro hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    cases n with
    | zero => exact Set.mem_iUnion.mpr ⟨0, hx hkn⟩
    | succ n => exact Set.mem_iUnion.mpr ⟨n, hkn⟩

theorem lfpAbove_ub {f : Pomega → Pomega} {A : Set Pomega} :
    ∀ x ∈ A, x ⊆ lfpAbove f (⋃₀ A) := by
  intro x hx k hk
  exact Set.mem_iUnion.mpr ⟨0, Set.subset_sUnion_of_mem hx hk⟩

theorem lfpAbove_le_of_ub {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {A : Set Pomega} {z : Pomega} (hz : f z = z) (hub : ∀ x ∈ A, x ⊆ z) :
    lfpAbove f (⋃₀ A) ⊆ z := by
  have h0 : ⋃₀ A ⊆ z := by
    intro k hk
    obtain ⟨x, hxA, hkx⟩ := Set.mem_sUnion.mp hk
    exact hub x hxA hkx
  have hiter : ∀ n, iterateFrom f (⋃₀ A) n ⊆ z := by
    intro n
    induction n with
    | zero => simpa [iterateFrom] using h0
    | succ n ih => simpa [iterateFrom, hz] using isScottContinuous_monotone hf ih
  intro k hk
  obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
  exact hiter n hkn

theorem lfpAbove_mem {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {A : Set Pomega} (hA : A ⊆ Fixpoints f) :
    lfpAbove f (⋃₀ A) ∈ Fixpoints f :=
  lfpAbove_fixed hf (sUnion_Fixpoints_le_image hf hA)

theorem gfpBelow_subset (f : Pomega → Pomega) (b : Pomega) :
    gfpBelow f b ⊆ b := by
  intro k hk
  obtain ⟨x, hx, hkx⟩ := Set.mem_sUnion.mp hk
  exact (hx hkx).2

theorem gfpBelow_postfixed {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (b : Pomega) : gfpBelow f b ⊆ f (gfpBelow f b) ∩ b := by
  intro k hk
  obtain ⟨x, hx, hkx⟩ := Set.mem_sUnion.mp hk
  have hxz : x ⊆ gfpBelow f b := fun _ hm => Set.mem_sUnion.mpr ⟨x, hx, hm⟩
  exact ⟨isScottContinuous_monotone hf hxz (hx hkx).1, (hx hkx).2⟩

theorem gfpBelow_fixed_inter {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (b : Pomega) : f (gfpBelow f b) ∩ b = gfpBelow f b := by
  apply subset_antisymm
  · intro k hk
    refine Set.mem_sUnion.mpr ⟨f (gfpBelow f b) ∩ b, ?_, hk⟩
    have hle : gfpBelow f b ⊆ f (gfpBelow f b) ∩ b := gfpBelow_postfixed hf b
    have : f (gfpBelow f b) ⊆ f (f (gfpBelow f b) ∩ b) :=
      isScottContinuous_monotone hf hle
    intro m hm
    exact ⟨this hm.1, hm.2⟩
  · exact gfpBelow_postfixed hf b

/-- **Scott 1976, Theorem 4.1 (The lattice theorem), complete-lattice half.**
The inf `gfpBelow f (⋂ A)` is a fixed point of `f` itself. -/
theorem theorem_4_1_complete (f : Pomega → Pomega) (hf : IsScottContinuous f)
    (A : Set Pomega) (hA : A ⊆ Fixpoints f) :
    gfpBelow f (⋂₀ A) ∈ Fixpoints f := by
  let z := gfpBelow f (⋂₀ A)
  have hinter : f z ∩ ⋂₀ A = z := gfpBelow_fixed_inter hf (⋂₀ A)
  have hzle : z ⊆ ⋂₀ A := gfpBelow_subset f (⋂₀ A)
  have hfz : f z ⊆ ⋂₀ A := by
    intro k hk y hy
    have hzy : z ⊆ y := subset_trans hzle (Set.sInter_subset_of_mem hy)
    have : k ∈ f y := isScottContinuous_monotone hf hzy hk
    have hyf : f y = y := hA hy
    rwa [hyf] at this
  have : f z ∩ ⋂₀ A = f z := Set.inter_eq_left.mpr hfz
  change f z = z
  rwa [this] at hinter

theorem gfpBelow_isGLB {f : Pomega → Pomega} (_hf : IsScottContinuous f)
    {A : Set Pomega} (_hA : A ⊆ Fixpoints f) {z : Pomega}
    (hz : f z = z) (hlb : ∀ x ∈ A, z ⊆ x) :
    z ⊆ gfpBelow f (⋂₀ A) := by
  have hzI : z ⊆ ⋂₀ A := fun k hk y hy => hlb y hy hk
  have hpost : z ⊆ f z ∩ ⋂₀ A := fun k hk => ⟨by rwa [hz], hzI hk⟩
  exact fun k hk => Set.mem_sUnion.mpr ⟨z, hpost, hk⟩

/-- Image of a set of fixed-point subtypes. -/
def Fixpoints.vals {f : Pomega → Pomega} (A : Set (Fixpoints f)) : Set Pomega :=
  Subtype.val '' A

theorem Fixpoints.vals_subset {f : Pomega → Pomega} (A : Set (Fixpoints f)) :
    Fixpoints.vals A ⊆ Fixpoints f := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := hx
  exact y.property

@[instance_reducible]
def fixpointsCompleteLattice {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    CompleteLattice (Fixpoints f) :=
  letI : SupSet (Fixpoints f) :=
    ⟨fun A => ⟨lfpAbove f (⋃₀ (Fixpoints.vals A)),
      lfpAbove_mem hf (Fixpoints.vals_subset A)⟩⟩
  { completeLatticeOfSup (Fixpoints f) (fun A => by
      refine ⟨?ub, ?least⟩
      · intro x hx
        change (x : Pomega) ⊆ lfpAbove f (⋃₀ (Fixpoints.vals A))
        exact lfpAbove_ub x.val ⟨x, hx, rfl⟩
      · intro z hz
        change lfpAbove f (⋃₀ (Fixpoints.vals A)) ⊆ z
        exact lfpAbove_le_of_ub hf z.property (fun y hy => by
          obtain ⟨w, hwA, rfl⟩ := hy
          exact hz hwA)) with
    sInf := fun A => ⟨gfpBelow f (⋂₀ (Fixpoints.vals A)),
      theorem_4_1_complete f hf (Fixpoints.vals A) (Fixpoints.vals_subset A)⟩
    isGLB_sInf := fun A => by
      refine ⟨?lb, ?greatest⟩
      · intro x hx
        change gfpBelow f (⋂₀ (Fixpoints.vals A)) ⊆ x
        exact subset_trans (gfpBelow_subset f _)
          (Set.sInter_subset_of_mem ⟨x, hx, rfl⟩)
      · intro z hz
        change (z : Pomega) ⊆ gfpBelow f (⋂₀ (Fixpoints.vals A))
        exact gfpBelow_isGLB hf (Fixpoints.vals_subset A) z.property (fun y hy => by
          obtain ⟨w, hwA, rfl⟩ := hy
          exact hz hwA)
    bot := ⟨fix f, (theorem_1_4 hf).1⟩
    bot_le := fun x => (theorem_1_4 hf).2 x.val x.property }

noncomputable instance fixpointsFunOfCompleteLattice (a : Pomega) :
    CompleteLattice (Fixpoints (funOf a)) :=
  fixpointsCompleteLattice (funOf_isScottContinuous a)

theorem retract_app {a : Pomega} (ha : IsRetract a) (x : Pomega) :
    funOf a (funOf a x) = funOf a x := by
  have := congrArg (fun u => funOf u x) ha
  simpa [comp_app] using this.symm

/-- The canonical finite-image basis of the fixed-point lattice of a retract. -/
def retractBasis (a : Pomega) (x : Fixpoints (funOf a)) :
    Set (Fixpoints (funOf a)) :=
  {y | ∃ n, e n ⊆ x ∧ (y : Pomega) = funOf a (e n)}

theorem funOf_botElem (x : Pomega) : funOf botElem x = botElem := by
  ext m
  simp [funOf, botElem]

theorem graph_const_bot : graph (fun _ => botElem) = botElem := by
  ext p
  simp [graph, botElem]

/-- Strictness: `a(⊥) = ⊥`, equivalently `⊥ ⊑ a` for retracts. -/
def IsStrict (a : Pomega) : Prop :=
  funOf a botElem = botElem

/-- **Scott 1976, (4.16).** Diagonal combinator. -/
def diagC : Pomega := graph (fun u => pairSeq u u)

/-- **Scott 1976, (4.22).** Evaluation combinator. -/
def evalC : Pomega :=
  graph (fun u => funOf (funOf u (ofNat 0)) (funOf u (ofNat 1)))

/-- **Scott 1976, (4.23).** Currying combinator. -/
def curryC : Pomega :=
  graph (fun u => graph (fun x => graph (fun y => funOf u (pairSeq x y))))

/-- **Scott 1976, (4.7).** The integer functional
`int(u) = u ⊒ 0, (int(u−1) ⊒ u, u)`. -/
def intF (f : Pomega) : Pomega :=
  graph (fun u =>
    dcondSet u (ofNat 0) (dcondSet (funOf f (predSet u)) u u))

/-- **Scott 1976, (4.7).** Integer retract as the least fixed point. -/
def intR : Pomega := fix intF

/-- **Scott 1976, (4.38).** The tree functor. -/
def treeF (z : Pomega) : Pomega := plusR botElem (tensorR z z)

theorem bot_isRetract : IsRetract botElem := by
  unfold IsRetract comp botElem
  ext p
  simp [graph, funOf]

theorem iterates_areRetracts {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a)) :
    ∀ n, IsRetract (iterateBot F n)
  | 0 => by simpa [iterateBot] using bot_isRetract
  | n + 1 => by simpa [iterateBot] using hret _ (iterates_areRetracts hret n)

/-- The strict bottom retract is below every strict retract in Scott's
projection order. -/
theorem bot_retractLe {a : Pomega} (ha : IsStrict a) :
    retractLe botElem a := by
  constructor
  · unfold comp
    have h : (fun x => funOf botElem (funOf a x)) = fun _ => botElem := by
      funext x
      exact funOf_botElem (funOf a x)
    rw [h, graph_const_bot]
  · unfold comp
    have h : (fun x => funOf a (funOf botElem x)) = fun _ => botElem := by
      funext x
      rw [funOf_botElem, ha]
    rw [h, graph_const_bot]

/-- Strictness of all Kleene approximants of a strictness-preserving
retract functor. -/
theorem iterateBot_isStrict {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a)) :
    ∀ n, IsStrict (iterateBot F n)
  | 0 => by simp [iterateBot, IsStrict, funOf_botElem]
  | n + 1 =>
      hstrict _ (iterates_areRetracts hret n)
        (iterateBot_isStrict hret hstrict n)

/-- Projection-order monotonicity gives adjacent projection equations for
the Kleene chain. -/
theorem iterateBot_retractLe_succ {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b)) :
    ∀ n, retractLe (iterateBot F n) (iterateBot F (n + 1))
  | 0 => by
      simpa [iterateBot] using
        (bot_retractLe (iterateBot_isStrict hret hstrict 1))
  | n + 1 => by
      simpa only [iterateBot] using
        hmono (iterates_areRetracts hret n) (iterateBot_isStrict hret hstrict n)
          (iterates_areRetracts hret (n + 1))
          (iterateBot_isStrict hret hstrict (n + 1))
          (iterateBot_retractLe_succ hret hstrict hmono n)

/-- Projection equations between arbitrary comparable Kleene stages. -/
theorem iterateBot_retractLe {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    {n m : ℕ} (hnm : n ≤ m) :
    retractLe (iterateBot F n) (iterateBot F m) := by
  induction m, hnm using Nat.le_induction with
  | base =>
      exact retractLe_refl (iterates_areRetracts hret n)
  | succ m _ ih =>
      exact retractLe_trans ih (iterateBot_retractLe_succ hret hstrict hmono m)

/-- The inverse limit of the ranges of `Fⁿ(⊥)`: points are typed at every
stage and adjacent coordinates satisfy Scott's projection equation. -/
def RetractInverseLimit (F : Pomega → Pomega) :=
  {v : ℕ → Pomega //
    (∀ n, typed (v n) (iterateBot F n)) ∧
      ∀ n, v n = funOf (iterateBot F n) (v (n + 1))}

instance (F : Pomega → Pomega) : PartialOrder (RetractInverseLimit F) where
  le v w := ∀ n, v.1 n ⊆ w.1 n
  le_refl _ _ := subset_rfl
  le_trans _ _ _ hvw hwz n := subset_trans (hvw n) (hwz n)
  le_antisymm v w hvw hwv := by
    apply Subtype.ext
    funext n
    exact Set.Subset.antisymm (hvw n) (hwv n)

/-- A coherent inverse-limit sequence is increasing in the ambient
powerset order. -/
theorem inverseLimit_mono {F : Pomega → Pomega}
    (hf : IsScottContinuous F) (v : RetractInverseLimit F) :
    ∀ n, v.1 n ⊆ v.1 (n + 1) := by
  intro n
  rw [v.property.2 n]
  have hcode : iterateBot F n ⊆ iterateBot F (n + 1) :=
    iterateBot_mono hf n
  have h := funOf_monotone_left hcode (v.1 (n + 1))
  rw [← v.property.1 (n + 1)] at h
  exact h

theorem inverseLimit_chain {F : Pomega → Pomega}
    (hf : IsScottContinuous F) (v : RetractInverseLimit F) :
    ∀ n m, n ≤ m → v.1 n ⊆ v.1 m :=
  chain_mono v.1 (inverseLimit_mono hf v)

/-- Repeated coherence: every later coordinate projects to an earlier one. -/
theorem inverseLimit_project_later {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) {n m : ℕ} (hnm : n ≤ m) :
    funOf (iterateBot F n) (v.1 m) = v.1 n := by
  induction m, hnm using Nat.le_induction with
  | base => exact (v.property.1 n).symm
  | succ m hnm ih =>
      have hle := iterateBot_retractLe hret hstrict hmono hnm
      have happ :=
        congrArg (fun a => funOf a (v.1 (m + 1))) hle.1
      rw [comp_app, ← v.property.2 m, ih] at happ
      exact happ

/-- Earlier typed coordinates are fixed by every later projection. -/
theorem inverseLimit_project_earlier {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) {m n : ℕ} (hmn : m ≤ n) :
    funOf (iterateBot F n) (v.1 m) = v.1 m := by
  have hle := iterateBot_retractLe hret hstrict hmono hmn
  have hm : funOf (iterateBot F m) (v.1 m) = v.1 m :=
    (v.property.1 m).symm
  have happ := congrArg (fun a => funOf a (v.1 m)) hle.2
  simpa only [comp_app, hm] using happ.symm

/-- Every stage projection of the union of a coherent sequence is its
corresponding coordinate. -/
theorem inverseLimit_project_iUnion {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) (n : ℕ) :
    funOf (iterateBot F n) (⋃ m, v.1 m) = v.1 n := by
  rw [chain_lemma (funOf_isScottContinuous (iterateBot F n)) v.1
    (inverseLimit_mono hf v)]
  apply subset_antisymm
  · intro k hk
    obtain ⟨m, hkm⟩ := Set.mem_iUnion.mp hk
    by_cases hmn : m ≤ n
    · rw [inverseLimit_project_earlier hret hstrict hmono v hmn] at hkm
      exact inverseLimit_chain hf v m n hmn hkm
    · have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
      rwa [inverseLimit_project_later hret hstrict hmono v hnm] at hkm
  · intro k hk
    exact Set.mem_iUnion.mpr ⟨n, by
      rw [inverseLimit_project_later hret hstrict hmono v (le_refl n)]
      exact hk⟩

/-- The union of a coherent sequence lies in the range of the least fixed
point retract. -/
theorem inverseLimit_iUnion_typed {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) :
    typed (⋃ n, v.1 n) (fix F) := by
  change (⋃ n, v.1 n) = funOf (fix F) (⋃ n, v.1 n)
  rw [fix, funOf_iUnion]
  apply Eq.symm
  congr 1
  funext n
  exact inverseLimit_project_iUnion hf hret hstrict hmono v n

/-- A point of the fixed-point range determines its sequence of finite
projections. -/
def fixedToInverseLimit {F : Pomega → Pomega}
    (_hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (u : Fixpoints (funOf (fix F))) : RetractInverseLimit F :=
  ⟨fun n => funOf (iterateBot F n) u.1,
    ⟨fun n => (retract_app (iterates_areRetracts hret n) u.1).symm,
      fun n => by
        have hle := iterateBot_retractLe_succ hret hstrict hmono n
        have happ := congrArg (fun a => funOf a u.1) hle.1
        simpa only [comp_app] using happ⟩⟩

/-- A coherent sequence determines a point of the least fixed-point range
by taking the union of its coordinates. -/
def inverseLimitToFixed {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) : Fixpoints (funOf (fix F)) :=
  ⟨⋃ n, v.1 n, (inverseLimit_iUnion_typed hf hret hstrict hmono v).symm⟩

/-- **Scott 1976, Theorem 4.6, inverse-limit half.** The maps
`u ↦ (Fⁿ(⊥)(u))ₙ` and `(vₙ) ↦ ⋃ₙ vₙ` are inverse order isomorphisms. -/
def theorem_4_6_inverseLimit {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b)) :
    Fixpoints (funOf (fix F)) ≃o RetractInverseLimit F where
  toFun := fixedToInverseLimit hf hret hstrict hmono
  invFun := inverseLimitToFixed hf hret hstrict hmono
  left_inv u := by
    apply Subtype.ext
    change (⋃ n, funOf (iterateBot F n) u.1) = u.1
    rw [← funOf_iUnion, ← fix, u.property]
  right_inv v := by
    apply Subtype.ext
    funext n
    exact inverseLimit_project_iUnion hf hret hstrict hmono v n
  map_rel_iff' := by
    intro u w
    constructor
    · intro h
      change ∀ n, funOf (iterateBot F n) u.1 ⊆
        funOf (iterateBot F n) w.1 at h
      change u.1 ⊆ w.1
      have hu : u.1 = ⋃ n, funOf (iterateBot F n) u.1 := by
        calc
          u.1 = funOf (fix F) u.1 := u.property.symm
          _ = ⋃ n, funOf (iterateBot F n) u.1 := by
            change funOf (⋃ n, iterateBot F n) u.1 = _
            rw [funOf_iUnion]
      have hw : w.1 = ⋃ n, funOf (iterateBot F n) w.1 := by
        calc
          w.1 = funOf (fix F) w.1 := w.property.symm
          _ = ⋃ n, funOf (iterateBot F n) w.1 := by
            change funOf (⋃ n, iterateBot F n) w.1 = _
            rw [funOf_iUnion]
      rw [hu, hw]
      intro k hk
      obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
      exact Set.mem_iUnion.mpr ⟨n, h n hkn⟩
    · intro huw
      change u.1 ⊆ w.1 at huw
      change ∀ n, funOf (iterateBot F n) u.1 ⊆
        funOf (iterateBot F n) w.1
      intro n
      exact funOf_monotone_right (iterateBot F n) huw

def treeR : Pomega := funOf Ycomb (graph treeF)

/-- **Scott 1976, (4.3).** Boolean retract via the doubly strict conditional. -/
def boolR : Pomega :=
  graph (fun u => dcondSet u (ofNat 0) (ofNat 1))

/-- **Scott 1976, (4.6).** The open-set retract. -/
def openR : Pomega :=
  graph (fun u => {m | ∃ n, e n ⊆ e m ∧ n ∈ u})

/-- **Scott 1976, (4.39).** `lamb = int ⊕ (lamb ∘→ lamb)`. -/
def lambF (z : Pomega) : Pomega := plusR intR (arrowR z z)

def lambR : Pomega := funOf Ycomb (graph lambF)

/-- **Scott 1976, (4.40).** `env = λt. lamb ∘ seq(t)`. -/
def envR : Pomega :=
  graph (fun t => graph (fun n => funOf lambR (funOf t n)))

/-- **Scott 1976, (4.41).** Environment update `t[x/n]`. -/
def updateEnv (t x : Pomega) (n : ℕ) : Pomega :=
  graph (fun m => if m = ofNat n then x else funOf t m)

/-- Tag injection `⟨i, x⟩` used by the expanded n-ary sum of (4.44). -/
def tagInj (i : ℕ) (x : Pomega) : Pomega := pairSeq (ofNat i) x

/-- Four-place sequence used by the expanded product of (4.44). -/
def seq4 (a b c d : Pomega) : Pomega :=
  graph (fun z =>
    condSet z a
      (condSet (predSet z) b
        (condSet (predSet (predSet z)) c
          (condSet (predSet (predSet (predSet z))) d botElem))))

/-- **Scott 1976, before (4.44).** Four-fold product by expanded indices,
not iterated binary `⊗`. -/
def tensor4 (a b c d : Pomega) : Pomega :=
  graph (fun u =>
    seq4 (funOf a (funOf u (ofNat 0)))
      (funOf b (funOf u (ofNat 1)))
      (funOf c (funOf u (ofNat 2)))
      (funOf d (funOf u (ofNat 3))))

/-- Body of the seven-way tagged sum of (4.44). -/
def plus7Body (a0 a1 a2 a3 a4 a5 a6 u : Pomega) : Pomega :=
  dcondSet (funOf u (ofNat 0)) (tagInj 0 (funOf a0 (funOf u (ofNat 1))))
    (dcondSet (predSet (funOf u (ofNat 0))) (tagInj 1 (funOf a1 (funOf u (ofNat 1))))
      (dcondSet (predSet (predSet (funOf u (ofNat 0))))
        (tagInj 2 (funOf a2 (funOf u (ofNat 1))))
        (dcondSet (predSet^[3] (funOf u (ofNat 0)))
          (tagInj 3 (funOf a3 (funOf u (ofNat 1))))
          (dcondSet (predSet^[4] (funOf u (ofNat 0)))
            (tagInj 4 (funOf a4 (funOf u (ofNat 1))))
            (dcondSet (predSet^[5] (funOf u (ofNat 0)))
              (tagInj 5 (funOf a5 (funOf u (ofNat 1))))
              (dcondSet (predSet^[6] (funOf u (ofNat 0)))
                (tagInj 6 (funOf a6 (funOf u (ofNat 1))))
                topElem))))))

/-- Seven-way tagged sum with indices `0,...,6`, dispatching by iterated
predecessor on the tag so mixed tags collapse to `⊤` as in (4.4). -/
def plus7 (a0 a1 a2 a3 a4 a5 a6 : Pomega) : Pomega :=
  graph (plus7Body a0 a1 a2 a3 a4 a5 a6)

/-- **Scott 1976, (4.44).** Abstract-syntax functor. -/
def expF (z : Pomega) : Pomega :=
  plus7 intR botElem z z (tensor4 z z z z) (tensorR z z) (tensorR intR z)

/-- **Scott 1976, (4.44).** `exp` as the least fixed point of the seven-tag
syntax functor. -/
def expR : Pomega := funOf Ycomb (graph expF)
end DomainTheory.DataTypesAsLattices
