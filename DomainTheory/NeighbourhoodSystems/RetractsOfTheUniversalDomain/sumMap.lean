module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_9

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

namespace sumMap

universe u

variable {γ δ γ' δ' γ'' δ'' : Type u}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

variable {h0 : ∀ X, V0.mem X → X.Nonempty} {h1 : ∀ Y, V1.mem Y → Y.Nonempty}

variable {h0' : ∀ X, V0'.mem X → X.Nonempty} {h1' : ∀ Y, V1'.mem Y → Y.Nonempty}

variable {h0'' : ∀ X, V0''.mem X → X.Nonempty} {h1'' : ∀ Y, V1''.mem Y → Y.Nonempty}

theorem reaches_neither_iff_eq_bot {y : (sum V0 V1 h0 h1).Element} :
    (∀ W, y.mem W → W = (sum V0 V1 h0 h1).master) ↔ y = (sum V0 V1 h0 h1).bot := by
  constructor
  · intro hN
    apply Element.ext
    intro W
    rw [mem_bot]
    exact ⟨hN W, fun h => h ▸ y.master_mem⟩
  · rintro rfl W hW
    rw [mem_bot] at hW
    exact hW

theorem bot (f : ApproximableMap V0 V0') (g : ApproximableMap V1 V1') :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
        (sum V0 V1 h0 h1).bot = (sum V0' V1' h0' h1').bot := by
  apply Element.ext
  intro Z
  rw [mem_bot]
  constructor
  · rintro ⟨W, hW, _, hZmem, hd⟩
    rw [mem_bot] at hW
    subst hW
    rcases hd with rfl | ⟨X, Y', hWX, -, -⟩ | ⟨Y, Y', hWY, -, -⟩
    · rfl
    · have hWX' : sumMaster V0 V1 = inj₀ X := hWX
      exact absurd (hWX' ▸ none_mem_sumMaster) none_mem_inj₀
    · have hWY' : sumMaster V0 V1 = inj₁ Y := hWY
      exact absurd (hWY' ▸ none_mem_sumMaster) none_mem_inj₁
  · rintro rfl
    exact ⟨sumMaster V0 V1, (sum V0 V1 h0 h1).mem_bot.mpr rfl, (sum V0 V1 h0 h1).master_mem,
      (sum V0' V1' h0' h1').master_mem, Or.inl rfl⟩

theorem reaches_left {f : ApproximableMap V0 V0'} {g : ApproximableMap V1 V1'}
    {y : (sum V0 V1 h0 h1).Element} (hL : ∃ X, V0.mem X ∧ y.mem (inj₀ X)) :
    ∃ X', V0'.mem X' ∧ ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
      y).mem (inj₀ X') := by
  obtain ⟨X, hX, hXy⟩ := hL
  have hf : f.rel X V0'.master :=
    f.mono f.master_rel (V0.sub_master hX) subset_rfl hX V0'.master_mem
  exact ⟨V0'.master, V0'.master_mem, inj₀ X, hXy,
    Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨V0'.master, V0'.master_mem, rfl⟩),
    Or.inr (Or.inl ⟨X, V0'.master, rfl, rfl, hf⟩)⟩

theorem reaches_right {f : ApproximableMap V0 V0'} {g : ApproximableMap V1 V1'}
    {y : (sum V0 V1 h0 h1).Element} (hR : ∃ Y, V1.mem Y ∧ y.mem (inj₁ Y)) :
    ∃ Y', V1'.mem Y' ∧ ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
      y).mem (inj₁ Y') := by
  obtain ⟨Y, hY, hYy⟩ := hR
  have hg : g.rel Y V1'.master :=
    g.mono g.master_rel (V1.sub_master hY) subset_rfl hY V1'.master_mem
  exact ⟨V1'.master, V1'.master_mem, inj₁ Y, hYy,
    Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨V1'.master, V1'.master_mem, rfl⟩),
    Or.inr (Or.inr ⟨Y, V1'.master, rfl, rfl, hg⟩)⟩

variable {γ δ γ' δ' γ'' δ'' : Type u}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

variable {h0 : ∀ X, V0.mem X → X.Nonempty} {h1 : ∀ Y, V1.mem Y → Y.Nonempty}

variable {h0' : ∀ X, V0'.mem X → X.Nonempty} {h1' : ∀ Y, V1'.mem Y → Y.Nonempty}

variable {h0'' : ∀ X, V0''.mem X → X.Nonempty} {h1'' : ∀ Y, V1''.mem Y → Y.Nonempty}

theorem toElementMap_inMap₀ (f : ApproximableMap V0 V0') (g : ApproximableMap V1 V1')
    (v : V0.Element) :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
        ((inMap₀ (h₀ := h0) (h₁ := h1)).toElementMap v) =
      (inMap₀ (h₀ := h0') (h₁ := h1')).toElementMap (f.toElementMap v) := by
  set z := (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
    ((inMap₀ (h₀ := h0) (h₁ := h1)).toElementMap v) with hz
  have hLz : ∃ X', V0'.mem X' ∧ z.mem (inj₀ X') :=
    reaches_left (inMap₀_toElementMap_reaches_left v)
  rw [← inMap₀_outMap₀_eq_of_left hLz]
  congr 1
  have heq : (outMap₀ (h₀ := h0') (h₁ := h1')).comp
      ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
        (inMap₀ (h₀ := h0) (h₁ := h1))) = f :=
    outMap₀_comp_sumMap_comp_inMap₀ f g
  calc (outMap₀ (h₀ := h0') (h₁ := h1')).toElementMap z
      = ((outMap₀ (h₀ := h0') (h₁ := h1')).comp
          ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
            (inMap₀ (h₀ := h0) (h₁ := h1)))).toElementMap v := by
        rw [toElementMap_comp, toElementMap_comp, ← hz]
    _ = f.toElementMap v := by rw [heq]

theorem toElementMap_inMap₁ (f : ApproximableMap V0 V0') (g : ApproximableMap V1 V1')
    (w : V1.Element) :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
        ((inMap₁ (h₀ := h0) (h₁ := h1)).toElementMap w) =
      (inMap₁ (h₀ := h0') (h₁ := h1')).toElementMap (g.toElementMap w) := by
  set z := (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
    ((inMap₁ (h₀ := h0) (h₁ := h1)).toElementMap w) with hz
  have hRz : ∃ Y', V1'.mem Y' ∧ z.mem (inj₁ Y') :=
    reaches_right (inMap₁_toElementMap_reaches_right w)
  rw [← inMap₁_outMap₁_eq_of_right hRz]
  congr 1
  have heq : (outMap₁ (h₀ := h0') (h₁ := h1')).comp
      ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
        (inMap₁ (h₀ := h0) (h₁ := h1))) = g :=
    outMap₁_comp_sumMap_comp_inMap₁ f g
  calc (outMap₁ (h₀ := h0') (h₁ := h1')).toElementMap z
      = ((outMap₁ (h₀ := h0') (h₁ := h1')).comp
          ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
            (inMap₁ (h₀ := h0) (h₁ := h1)))).toElementMap w := by
        rw [toElementMap_comp, toElementMap_comp, ← hz]
    _ = g.toElementMap w := by rw [heq]

theorem toElementMap_of_left {f : ApproximableMap V0 V0'} {g : ApproximableMap V1 V1'}
    {y : (sum V0 V1 h0 h1).Element} (hL : ∃ X, V0.mem X ∧ y.mem (inj₀ X)) :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap y =
      (inMap₀ (h₀ := h0') (h₁ := h1')).toElementMap
        (f.toElementMap ((outMap₀ (h₀ := h0) (h₁ := h1)).toElementMap y)) := by
  conv_lhs => rw [← inMap₀_outMap₀_eq_of_left hL]
  exact toElementMap_inMap₀ f g _

theorem toElementMap_of_right {f : ApproximableMap V0 V0'} {g : ApproximableMap V1 V1'}
    {y : (sum V0 V1 h0 h1).Element} (hR : ∃ Y, V1.mem Y ∧ y.mem (inj₁ Y)) :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap y =
      (inMap₁ (h₀ := h0') (h₁ := h1')).toElementMap
        (g.toElementMap ((outMap₁ (h₀ := h0) (h₁ := h1)).toElementMap y)) := by
  conv_lhs => rw [← inMap₁_outMap₁_eq_of_right hR]
  exact toElementMap_inMap₁ f g _

variable {γ δ γ' δ' γ'' δ'' : Type u}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

variable {h0 : ∀ X, V0.mem X → X.Nonempty} {h1 : ∀ Y, V1.mem Y → Y.Nonempty}

variable {h0' : ∀ X, V0'.mem X → X.Nonempty} {h1' : ∀ Y, V1'.mem Y → Y.Nonempty}

variable {h0'' : ∀ X, V0''.mem X → X.Nonempty} {h1'' : ∀ Y, V1''.mem Y → Y.Nonempty}

theorem comp (f' : ApproximableMap V0' V0'') (f : ApproximableMap V0 V0')
    (g' : ApproximableMap V1' V1'') (g : ApproximableMap V1 V1') :
    sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0'') (h₁' := h1'') (f'.comp f) (g'.comp g) =
      (sumMap (h₀ := h0') (h₁ := h1') (h₀' := h0'') (h₁' := h1'') f' g').comp
        (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g) := by
  apply ext_of_toElementMap
  intro y
  rw [toElementMap_comp]
  rcases sum_element_trichotomy y with hL | hR | hN
  · rw [toElementMap_of_left hL, toElementMap_comp, toElementMap_of_left hL,
      toElementMap_of_left (inMap₀_toElementMap_reaches_left _),
      toElementMap_of_comp_eq_idMap outMap₀_comp_inMap₀]
  · rw [toElementMap_of_right hR, toElementMap_comp, toElementMap_of_right hR,
      toElementMap_of_right (inMap₁_toElementMap_reaches_right _),
      toElementMap_of_comp_eq_idMap outMap₁_comp_inMap₁]
  · rw [reaches_neither_iff_eq_bot] at hN
    rw [hN, bot, bot, bot]

variable {γ δ γ' δ' γ'' δ'' : Type u}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

variable {h0 : ∀ X, V0.mem X → X.Nonempty} {h1 : ∀ Y, V1.mem Y → Y.Nonempty}

variable {h0' : ∀ X, V0'.mem X → X.Nonempty} {h1' : ∀ Y, V1'.mem Y → Y.Nonempty}

variable {h0'' : ∀ X, V0''.mem X → X.Nonempty} {h1'' : ∀ Y, V1''.mem Y → Y.Nonempty}

theorem id : sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0) (h₁' := h1)
    (idMap V0) (idMap V1) = idMap (sum V0 V1 h0 h1) := by
  apply ext_of_toElementMap
  intro y
  rw [toElementMap_idMap]
  rcases sum_element_trichotomy y with hL | hR | hN
  · rw [toElementMap_of_left hL, toElementMap_idMap, inMap₀_outMap₀_eq_of_left hL]
  · rw [toElementMap_of_right hR, toElementMap_idMap, inMap₁_outMap₁_eq_of_right hR]
  · rw [reaches_neither_iff_eq_bot] at hN
    rw [hN, bot]

end sumMap

end DomainTheory.NeighbourhoodSystems
