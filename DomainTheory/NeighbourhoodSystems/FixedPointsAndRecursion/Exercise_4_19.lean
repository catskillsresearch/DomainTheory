module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example_4_4
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise419
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44

section
variable {β : Type*}

notation "𝕥" => Example23.trueElt

notation "𝕗" => Example23.falseElt

def headValC (V : NeighborhoodSystem β) (z a0 a1 : V.Element) : Str → V.Element
  | [] => z
  | false :: _ => a0
  | true :: _ => a1

@[simp] theorem headValC_nil (V : NeighborhoodSystem β) (z a0 a1 : V.Element) :
    headValC V z a0 a1 [] = z := rfl

@[simp] theorem headValC_false (V : NeighborhoodSystem β) (z a0 a1 : V.Element) (σ : Str) :
    headValC V z a0 a1 (false :: σ) = a0 := rfl

@[simp] theorem headValC_true (V : NeighborhoodSystem β) (z a0 a1 : V.Element) (σ : Str) :
    headValC V z a0 a1 (true :: σ) = a1 := rfl

abbrev T : NeighborhoodSystem Example12.Token := Example23.T

theorem headValC_bot_le (V : NeighborhoodSystem β) (z' a0 a1 : V.Element) {σ τ : Str}
    (h : σ <+: τ) : headValC V V.bot a0 a1 σ ≤ headValC V z' a0 a1 τ := by
  cases σ with
  | nil => exact bot_le
  | cons b σ0 =>
    obtain ⟨s, rfl⟩ := h
    cases b
    · rw [List.cons_append]; exact le_of_eq rfl
    · rw [List.cons_append]; exact le_of_eq rfl
end

section

theorem not_cone_subset_singleton (τ σ : Str) : ¬ cone τ ⊆ ({σ} : Set Str) := by
  intro h
  have h1 : τ ∈ ({σ} : Set Str) := h (by simp [mem_cone])
  have h2 : (τ ++ [true]) ∈ ({σ} : Set Str) := h (by simp [mem_cone])
  rw [Set.mem_singleton_iff] at h1 h2
  have : τ = τ ++ [true] := h1.trans h2.symm
  simp at this
end

section

theorem cone_ne_singleton (τ σ : Str) : cone τ ≠ ({σ} : Set Str) := by
  intro h
  exact not_cone_subset_singleton τ σ (h ▸ subset_rfl)
end

section
variable {β : Type*}

def liftC (V : NeighborhoodSystem β) (coneVal singVal : Str → V.Element)
    (hcone : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ singVal τ) :
    ApproximableMap C V where
  rel X Y := (∃ σ, X = cone σ ∧ (coneVal σ).mem Y) ∨ (∃ σ, X = {σ} ∧ (singVal σ).mem Y)
  rel_dom := by
    rintro X Y (⟨σ, rfl, _⟩ | ⟨σ, rfl, _⟩)
    · exact memC_cone σ
    · exact memC_singleton σ
  rel_cod := by
    rintro X Y (⟨σ, _, hY⟩ | ⟨σ, _, hY⟩)
    · exact (coneVal σ).sub hY
    · exact (singVal σ).sub hY
  master_rel := by
    refine Or.inl ⟨[], ?_, (coneVal []).master_mem⟩
    rw [C_master]; exact cone_nil.symm
  inter_right := by
    rintro X Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) (⟨σ', hX', hY'⟩ | ⟨σ', hX', hY'⟩)
    · have : σ = σ' := cone_injective hX'
      subst this
      exact Or.inl ⟨σ, rfl, (coneVal σ).inter_mem hY hY'⟩
    · exact absurd hX' (cone_ne_singleton σ σ')
    · exact absurd hX'.symm (cone_ne_singleton σ' σ)
    · have : σ = σ' := by rw [Set.singleton_eq_singleton_iff] at hX'; exact hX'
      subst this
      exact Or.inr ⟨σ, rfl, (singVal σ).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) hX'X hYY' hX' hY'
    ·
      rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      ·
        have hpre : σ <+: τ := cone_subset_cone.mp hX'X
        exact Or.inl ⟨τ, rfl, (coneVal τ).up_mem (hcone hpre Y hY) hY' hYY'⟩
      ·
        have hpre : σ <+: τ := singleton_subset_cone.mp hX'X
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem (hsing hpre Y hY) hY' hYY'⟩
    ·
      rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · exact absurd hX'X (not_cone_subset_singleton τ σ)
      · have hτσ : τ = σ := by
          have := Set.singleton_subset_iff.mp hX'X
          rwa [Set.mem_singleton_iff] at this
        subst hτσ
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem hY hY' hYY'⟩

def emptyMap : ApproximableMap C T :=
  liftC T (headValC T T.bot 𝕗 𝕗) (headValC T 𝕥 𝕗 𝕗)
    (headValC_bot_le T T.bot 𝕗 𝕗) (headValC_bot_le T 𝕥 𝕗 𝕗)

theorem liftC_strBot (V : NeighborhoodSystem β) (coneVal singVal : Str → V.Element)
    (hcone : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Str) :
    (liftC V coneVal singVal hcone hsing).toElementMap (strBot σ) = coneVal σ := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := cone_subset_cone.mp (hXcone ▸ hsub)
      exact hcone hpre Y hY
    · exact absurd (hXsing ▸ hsub) (not_cone_subset_singleton σ σ')
  · intro hY
    exact ⟨cone σ, ⟨memC_cone σ, subset_rfl⟩, Or.inl ⟨σ, rfl, hY⟩⟩

theorem liftC_strElem (V : NeighborhoodSystem β) (coneVal singVal : Str → V.Element)
    (hcone : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Str) :
    (liftC V coneVal singVal hcone hsing).toElementMap (strElem σ) = singVal σ := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := by
        apply singleton_subset_cone.mp
        rw [← hXcone]; exact hsub
      exact hsing hpre Y hY
    · have hσσ' : σ = σ' := by
        have := Set.singleton_subset_iff.mp (hXsing ▸ hsub)
        rwa [Set.mem_singleton_iff] at this
      subst hσσ'; exact hY
  · intro hY
    exact ⟨{σ}, ⟨memC_singleton σ, subset_rfl⟩, Or.inr ⟨σ, rfl, hY⟩⟩

@[simp] theorem emptyMap_strElem (σ : Str) :
    emptyMap.toElementMap (strElem σ) = headValC T 𝕥 𝕗 𝕗 σ :=
  liftC_strElem T (headValC T T.bot 𝕗 𝕗) (headValC T 𝕥 𝕗 𝕗)
    (headValC_bot_le T T.bot 𝕗 𝕗) (headValC_bot_le T 𝕥 𝕗 𝕗) σ

@[simp] theorem emptyMap_strBot (σ : Str) :
    emptyMap.toElementMap (strBot σ) = headValC T T.bot 𝕗 𝕗 σ :=
  liftC_strBot T (headValC T T.bot 𝕗 𝕗) (headValC T 𝕥 𝕗 𝕗)
    (headValC_bot_le T T.bot 𝕗 𝕗) (headValC_bot_le T 𝕥 𝕗 𝕗) σ

def oneMap : ApproximableMap C T :=
  liftC T (headValC T T.bot 𝕗 𝕥) (headValC T 𝕗 𝕗 𝕥)
    (headValC_bot_le T T.bot 𝕗 𝕥) (headValC_bot_le T 𝕗 𝕗 𝕥)

def zeroMap : ApproximableMap C T :=
  liftC T (headValC T T.bot 𝕥 𝕗) (headValC T 𝕗 𝕥 𝕗)
    (headValC_bot_le T T.bot 𝕥 𝕗) (headValC_bot_le T 𝕗 𝕥 𝕗)

@[simp] theorem zeroMap_strElem (σ : Str) :
    zeroMap.toElementMap (strElem σ) = headValC T 𝕗 𝕥 𝕗 σ :=
  liftC_strElem T (headValC T T.bot 𝕥 𝕗) (headValC T 𝕗 𝕥 𝕗)
    (headValC_bot_le T T.bot 𝕥 𝕗) (headValC_bot_le T 𝕗 𝕥 𝕗) σ

@[simp] theorem zeroMap_strBot (σ : Str) :
    zeroMap.toElementMap (strBot σ) = headValC T T.bot 𝕥 𝕗 σ :=
  liftC_strBot T (headValC T T.bot 𝕥 𝕗) (headValC T 𝕗 𝕥 𝕗)
    (headValC_bot_le T T.bot 𝕥 𝕗) (headValC_bot_le T 𝕗 𝕥 𝕗) σ

@[simp] theorem oneMap_strElem (σ : Str) :
    oneMap.toElementMap (strElem σ) = headValC T 𝕗 𝕗 𝕥 σ :=
  liftC_strElem T (headValC T T.bot 𝕗 𝕥) (headValC T 𝕗 𝕗 𝕥)
    (headValC_bot_le T T.bot 𝕗 𝕥) (headValC_bot_le T 𝕗 𝕗 𝕥) σ

@[simp] theorem oneMap_strBot (σ : Str) :
    oneMap.toElementMap (strBot σ) = headValC T T.bot 𝕗 𝕥 σ :=
  liftC_strBot T (headValC T T.bot 𝕗 𝕥) (headValC T 𝕗 𝕗 𝕥)
    (headValC_bot_le T T.bot 𝕗 𝕥) (headValC_bot_le T 𝕗 𝕗 𝕥) σ

def oneDef (x : C.Element) : T.Element :=
  (Exercise326.cond T).toElementMap
    (pair (emptyMap.toElementMap x)
      (pair 𝕗
        ((Exercise326.cond T).toElementMap (pair (zeroMap.toElementMap x) (pair 𝕗 𝕥)))))

theorem condT_bot (x y : T.Element) :
    (Exercise326.cond T).toElementMap (pair T.bot (pair x y)) = T.bot := by
  apply Element.ext
  intro Z
  rw [Exercise326.cond_toElementMap_mem]
  constructor
  · rintro (⟨h0, _⟩ | ⟨h1, _⟩ | rfl)
    · rw [NeighborhoodSystem.mem_bot] at h0; exact absurd h0 Exercise326.zero_ne_master
    · rw [NeighborhoodSystem.mem_bot] at h1; exact absurd h1 Exercise326.one_ne_master
    · exact T.bot.master_mem
  · intro h
    rw [NeighborhoodSystem.mem_bot] at h
    exact Or.inr (Or.inr h)
end
end DomainTheory.NeighbourhoodSystems.Exercise419

section
namespace DomainTheory.NeighbourhoodSystems.Exercise419
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44
section
variable {β : Type*}

theorem one_def_strBot (σ : Str) : oneMap.toElementMap (strBot σ) = oneDef (strBot σ) := by
  cases σ with
  | nil =>
    rw [oneDef, emptyMap_strBot, headValC_nil, condT_bot, oneMap_strBot, headValC_nil]
  | cons b σ0 =>
    cases b with
    | false =>
      rw [oneDef, emptyMap_strBot, headValC_false, Exercise326.cond_false,
        zeroMap_strBot, headValC_false, Exercise326.cond_true, oneMap_strBot, headValC_false]
    | true =>
      rw [oneDef, emptyMap_strBot, headValC_true, Exercise326.cond_false,
        zeroMap_strBot, headValC_true, Exercise326.cond_false, oneMap_strBot, headValC_true]

theorem one_def_strElem (σ : Str) : oneMap.toElementMap (strElem σ) = oneDef (strElem σ) := by
  cases σ with
  | nil =>

    rw [oneDef, emptyMap_strElem, headValC_nil, Exercise326.cond_true,
      oneMap_strElem, headValC_nil]
  | cons b σ0 =>
    cases b with
    | false =>

      rw [oneDef, emptyMap_strElem, headValC_false, Exercise326.cond_false,
        zeroMap_strElem, headValC_false, Exercise326.cond_true, oneMap_strElem, headValC_false]
    | true =>
      rw [oneDef, emptyMap_strElem, headValC_true, Exercise326.cond_false,
        zeroMap_strElem, headValC_true, Exercise326.cond_false, oneMap_strElem, headValC_true]

end

section

theorem peano_cons_disjoint (σ τ : Str) : (false :: σ) ≠ (true :: τ) := by
  simp
end

section

theorem peano_cons_injective {b : Bool} {σ τ : Str} (h : b :: σ = b :: τ) : σ = τ :=
  (List.cons.injEq b σ b τ).mp h |>.2
end

section

theorem peano_induction (P : Str → Prop) (hnil : P []) (hcons : ∀ b σ, P σ → P (b :: σ)) :
    ∀ σ, P σ := by
  intro σ
  induction σ with
  | nil => exact hnil
  | cons b σ ih => exact hcons b σ ih
end

section

theorem peano_nil_ne_cons (b : Bool) (σ : Str) : ([] : Str) ≠ b :: σ := by
  simp
end

section
set_option linter.unusedVariables false

theorem example_419 : And
  (And
    (And
      (And
        (And
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))))
        (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
              DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))
            (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))))
      (∀ (σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @Ne (List Bool) (@List.cons Bool Bool.false σ) (@List.cons Bool Bool.true τ)))
    (∀ {b : Bool} {σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str},
      @Eq (List Bool) (@List.cons Bool b σ) (@List.cons Bool b τ) →
        @Eq DomainTheory.NeighbourhoodSystems.ExampleB.Str σ τ))
  (∀ (P : DomainTheory.NeighbourhoodSystems.ExampleB.Str → Prop),
    P (@List.nil Bool) →
      (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str), P σ → P (@List.cons Bool b σ)) →
        ∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str), P σ) :=
  @And.intro
  (And
    (And
      (And
        (And
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))))
        (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
              DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))
            (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))))
      (∀ (σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @Ne (List Bool) (@List.cons Bool Bool.false σ) (@List.cons Bool Bool.true τ)))
    (∀ {b : Bool} {σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str},
      @Eq (List Bool) (@List.cons Bool b σ) (@List.cons Bool b τ) →
        @Eq DomainTheory.NeighbourhoodSystems.ExampleB.Str σ τ))
  (∀ (P : DomainTheory.NeighbourhoodSystems.ExampleB.Str → Prop),
    P (@List.nil Bool) →
      (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str), P σ → P (@List.cons Bool b σ)) →
        ∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str), P σ)
  (@And.intro
    (And
      (And
        (And
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))))
        (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
              DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))
            (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))))
      (∀ (σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @Ne (List Bool) (@List.cons Bool Bool.false σ) (@List.cons Bool Bool.true τ)))
    (∀ {b : Bool} {σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str},
      @Eq (List Bool) (@List.cons Bool b σ) (@List.cons Bool b τ) →
        @Eq DomainTheory.NeighbourhoodSystems.ExampleB.Str σ τ)
    (@And.intro
      (And
        (And
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))))
        (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
              DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))
            (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))))
      (∀ (σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @Ne (List Bool) (@List.cons Bool Bool.false σ) (@List.cons Bool Bool.true τ))
      (@And.intro
        (And
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))))
        (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
              DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))
            (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ)))
        (@And.intro
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ)))
          DomainTheory.NeighbourhoodSystems.Exercise419.peano_nil_ne_cons
          DomainTheory.NeighbourhoodSystems.Exercise419.one_def_strBot)
        DomainTheory.NeighbourhoodSystems.Exercise419.one_def_strElem)
      DomainTheory.NeighbourhoodSystems.Exercise419.peano_cons_disjoint)
    @DomainTheory.NeighbourhoodSystems.Exercise419.peano_cons_injective)
  DomainTheory.NeighbourhoodSystems.Exercise419.peano_induction
end

end DomainTheory.NeighbourhoodSystems.Exercise419
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem comp_fixElement_isFixed (f g : ApproximableMap V V) :
    (f.comp g).toElementMap (f.toElementMap (g.comp f).fixElement)
      = f.toElementMap (g.comp f).fixElement := by
  rw [toElementMap_comp]

  have h : g.toElementMap (f.toElementMap (g.comp f).fixElement) = (g.comp f).fixElement := by
    rw [← toElementMap_comp]
    exact toElementMap_fixElement (g.comp f)
  rw [h]

end ApproximableMap
end
end DomainTheory.NeighbourhoodSystems
end
