module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_16
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Definition_3_8
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Examples_1_2_1_5_revisited
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Exercise317
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

abbrev T : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

abbrev Token := Example12.Token

theorem T_nbhd_nonempty {F : Set Token} (hF : T.mem F) : F.Nonempty := by
  rcases (Example12.mem_iff F).mp hF with rfl | rfl | rfl
  · exact ⟨0, by simp [Example12.master]⟩
  · exact ⟨0, by simp [Example12.zero]⟩
  · exact ⟨1, by simp [Example12.one]⟩

def bitNbhd : Bool → Set Token
  | false => Example12.zero
  | true => Example12.one

theorem bitNbhd_mem (b : Bool) : T.mem (bitNbhd b) := by
  cases b
  · exact Example12.mem_zero
  · exact Example12.mem_one

def encSet (σ : Str) : Set (ℕ × Token) := {p | ∀ b, σ[p.1]? = some b → p.2 ∈ bitNbhd b}

@[simp] theorem mem_encSet {σ : Str} {p : ℕ × Token} :
    p ∈ encSet σ ↔ ∀ b, σ[p.1]? = some b → p.2 ∈ bitNbhd b := Iff.rfl

@[simp] theorem encSet_nil : encSet [] = Set.univ := by
  ext p; simp [encSet]

theorem comparable_of_agree : ∀ {τ τ' : Str},
    (∀ (i : ℕ) (b b' : Bool), τ[i]? = some b → τ'[i]? = some b' → b = b') → τ <+: τ' ∨ τ' <+: τ
  | [], _, _ => Or.inl (List.nil_prefix)
  | _ :: _, [], _ => Or.inr (List.nil_prefix)
  | a :: s, a' :: s', hag => by
      have ha : a = a' := hag 0 a a' (by simp) (by simp)
      subst ha
      have hrec : ∀ (i : ℕ) (b b' : Bool), s[i]? = some b → s'[i]? = some b' → b = b' := by
        intro i b b' hb hb'
        exact hag (i + 1) b b' (by simpa using hb) (by simpa using hb')
      rcases comparable_of_agree hrec with h | h
      · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      · exact Or.inr (List.cons_prefix_cons.mpr ⟨rfl, h⟩)

theorem encSet_agree {τ τ' : Str} {W : Set (ℕ × Token)} (hW : (iterSys T).mem W)
    (h : W ⊆ encSet τ) (h' : W ⊆ encSet τ') {i : ℕ} {b b' : Bool}
    (hb : τ[i]? = some b) (hb' : τ'[i]? = some b') : b = b' := by
  obtain ⟨t, ht⟩ := T_nbhd_nonempty (hW.1 i)
  have h1 : t ∈ bitNbhd b := (h ht) b hb
  have h2 : t ∈ bitNbhd b' := (h' ht) b' hb'
  by_contra hne
  cases b <;> cases b' <;> simp_all [bitNbhd, Example12.zero, Example12.one]

theorem encSet_anti {σ σ' : Str} (h : σ <+: σ') : encSet σ' ⊆ encSet σ := by
  obtain ⟨t, rfl⟩ := h
  rintro ⟨i, x⟩ hp b hb
  have hi : i < σ.length := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hb; exact hlt
  exact hp b (by rw [List.getElem?_append_left hi]; exact hb)

theorem fiber_encSet_none {σ : Str} {i : ℕ} (h : σ[i]? = none) :
    fiber (encSet σ) i = Set.univ := by
  ext t
  simp only [mem_fiber, mem_encSet, Set.mem_univ, iff_true]
  intro b hb; rw [h] at hb; exact absurd hb (by simp)

theorem fiber_encSet_some {σ : Str} {i : ℕ} {b : Bool} (h : σ[i]? = some b) :
    fiber (encSet σ) i = bitNbhd b := by
  ext t
  simp only [mem_fiber, mem_encSet]
  constructor
  · intro hh; exact hh b h
  · intro ht b' hb'
    rw [h] at hb'
    obtain rfl := Option.some.inj hb'
    exact ht

theorem encSet_mem (σ : Str) : (iterSys T).mem (encSet σ) := by
  refine ⟨fun i => ?_, σ.length, fun i hi => ?_⟩
  · cases h : σ[i]? with
    | none => rw [fiber_encSet_none h]; exact T.master_mem
    | some b => rw [fiber_encSet_some h]; exact bitNbhd_mem b
  · rw [fiber_encSet_none (List.getElem?_eq_none_iff.mpr hi)]; rfl

def f : ApproximableMap B (iterSys T) where
  rel X W := ∃ σ, X = cone σ ∧ (iterSys T).mem W ∧ encSet σ ⊆ W
  rel_dom := fun ⟨σ, hX, _⟩ => hX ▸ memB_cone σ
  rel_cod := fun ⟨_, _, hW, _⟩ => hW
  master_rel := ⟨[], cone_nil.symm, (iterSys T).master_mem, by rw [encSet_nil]; exact Set.subset_univ _⟩
  inter_right := by
    rintro X W W' ⟨σ, hX, hWmem, hWsub⟩ ⟨σ', hX', hW'mem, hW'sub⟩
    obtain rfl : σ = σ' := cone_injective (hX.symm.trans hX')
    exact ⟨σ, hX, (iterSys T).inter_mem hWmem hW'mem (encSet_mem σ)
      (Set.subset_inter hWsub hW'sub), Set.subset_inter hWsub hW'sub⟩
  mono := by
    rintro X X' W W' ⟨σ, hX, _, hWsub⟩ hX'X hWW' hX' hW'mem
    obtain ⟨σ', rfl⟩ := hX'
    subst hX
    have hpre : σ <+: σ' := cone_subset_cone.mp hX'X
    exact ⟨σ', rfl, hW'mem, (encSet_anti hpre).trans (hWsub.trans hWW')⟩

def g : ApproximableMap (iterSys T) B where
  rel W X := (iterSys T).mem W ∧ ∃ τ, X = cone τ ∧ W ⊆ encSet τ
  rel_dom h := h.1
  rel_cod := fun ⟨_, τ, hX, _⟩ => hX ▸ memB_cone τ
  master_rel := ⟨(iterSys T).master_mem, [], cone_nil.symm, by rw [encSet_nil]; exact Set.subset_univ _⟩
  inter_right := by
    rintro W X X' ⟨hW, τ, hX, hWτ⟩ ⟨_, τ', hX', hWτ'⟩
    subst hX; subst hX'
    rcases comparable_of_agree (fun i b b' => encSet_agree hW hWτ hWτ') with hpre | hpre
    · exact ⟨hW, τ', by rw [Set.inter_eq_right.mpr (cone_subset_cone.mpr hpre)], hWτ'⟩
    · exact ⟨hW, τ, by rw [Set.inter_eq_left.mpr (cone_subset_cone.mpr hpre)], hWτ⟩
  mono := by
    rintro W W₂ X X₂ ⟨_, τ, hX, hWτ⟩ hW₂W hXX₂ hW₂ hX₂
    obtain ⟨τ₂, rfl⟩ := hX₂
    subst hX
    have hpre : τ₂ <+: τ := cone_subset_cone.mp hXX₂
    exact ⟨hW₂, τ₂, rfl, hW₂W.trans (hWτ.trans (encSet_anti hpre))⟩

theorem exists_not_mem_bitNbhd (b : Bool) : ∃ t : Token, t ∉ bitNbhd b := by
  cases b
  · exact ⟨1, by simp [bitNbhd, Example12.zero]⟩
  · exact ⟨0, by simp [bitNbhd, Example12.one]⟩

theorem fg_le_id : f.comp g ≤ idMap (iterSys T) := by
  intro W Z
  rw [comp_rel, idMap_rel]
  rintro ⟨X, ⟨hW, τ, hX, hWτ⟩, σ, hXσ, hZmem, hσZ⟩
  obtain rfl : τ = σ := cone_injective (hX.symm.trans hXσ)
  exact ⟨hW, hZmem, hWτ.trans hσZ⟩

theorem prefix_of_encSet_subset {σ τ : Str} (h : encSet σ ⊆ encSet τ) : τ <+: σ := by
  have hag : ∀ (i : ℕ) (b b' : Bool), σ[i]? = some b → τ[i]? = some b' → b = b' :=
    fun i b b' => encSet_agree (encSet_mem σ) subset_rfl h
  rcases comparable_of_agree hag with hστ | hτσ
  · by_cases hlen : σ.length = τ.length
    · exact (hστ.eq_of_length hlen) ▸ List.prefix_rfl
    · exfalso
      have hlt : σ.length < τ.length := lt_of_le_of_ne hστ.length_le hlen
      have hb' : τ[σ.length]? = some τ[σ.length] := List.getElem?_eq_getElem hlt
      obtain ⟨t, ht⟩ := exists_not_mem_bitNbhd τ[σ.length]
      have hmemσ : (σ.length, t) ∈ encSet σ := by
        intro b hb
        rw [List.getElem?_eq_none_iff.mpr (le_refl _)] at hb
        exact absurd hb (by simp)
      exact ht ((h hmemσ) _ hb')
  · exact hτσ

theorem gf_eq_id : g.comp f = idMap B := by
  apply ApproximableMap.ext
  intro X Y
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨σ, hX, _, hσW⟩, _, τ, hY, hWτ⟩
    refine ⟨hX ▸ memB_cone σ, hY ▸ memB_cone τ, ?_⟩
    have hsub : encSet σ ⊆ encSet τ := hσW.trans hWτ
    rw [hX, hY]
    exact cone_subset_cone.mpr (prefix_of_encSet_subset hsub)
  · rintro ⟨hX, hY, hXY⟩
    obtain ⟨σ, rfl⟩ := hX
    obtain ⟨τ, rfl⟩ := hY
    have hpre : τ <+: σ := cone_subset_cone.mp hXY
    exact ⟨encSet σ, ⟨σ, rfl, encSet_mem σ, subset_rfl⟩,
      encSet_mem σ, τ, rfl, encSet_anti hpre⟩

section
set_option linter.unusedVariables false

theorem example_317 : And
  (@LE.le
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T))
    (@Preorder.toLE
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
        (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
        (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise317.T)
        (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise317.T))
      (@PartialOrder.toPreorder
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T))
        (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T))))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token) DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.ExampleB.B
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.Exercise317.f DomainTheory.NeighbourhoodSystems.Exercise317.g)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
      DomainTheory.NeighbourhoodSystems.ExampleB.B)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token) DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.B
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise317.g
      DomainTheory.NeighbourhoodSystems.Exercise317.f)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.B)) :=
  @And.intro
  (@LE.le
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T))
    (@Preorder.toLE
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
        (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
        (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise317.T)
        (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise317.T))
      (@PartialOrder.toPreorder
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T))
        (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T))))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token) DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.ExampleB.B
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.Exercise317.f DomainTheory.NeighbourhoodSystems.Exercise317.g)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
      DomainTheory.NeighbourhoodSystems.ExampleB.B)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token) DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.B
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise317.g
      DomainTheory.NeighbourhoodSystems.Exercise317.f)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.B))
  DomainTheory.NeighbourhoodSystems.Exercise317.fg_le_id DomainTheory.NeighbourhoodSystems.Exercise317.gf_eq_id
end

theorem f_injective : Function.Injective f.toElementMap := by
  intro x y hxy
  have : (g.comp f).toElementMap x = (g.comp f).toElementMap y := by
    rw [toElementMap_comp, toElementMap_comp, hxy]
  rwa [gf_eq_id, toElementMap_idMap, toElementMap_idMap] at this
end

end DomainTheory.NeighbourhoodSystems.Exercise317
end
