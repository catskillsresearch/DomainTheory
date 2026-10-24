module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_20

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Exercise326
section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
section
variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
/- concordance: source L1585 EXERCISE 3.26 conditional combinator -/
/-- **Exercise 3.26.** `condSum(⊥, x, y) = ⊥`. -/
theorem condSum_bot (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.botElt (pair x y)) = (sum V₀ V₁ h₀ h₁).bot := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_bot]

/-- **Exercise 3.26.** `condSum(false, x, y) = in₁(y)`. -/
theorem condSum_false (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.falseElt (pair x y))
      = (inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_false]

/-- **Exercise 3.26.** `condSum(true, x, y) = in₀(x)`. -/
theorem condSum_true (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.trueElt (pair x y))
      = (inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_true]

/-- `∅` is never a sum-neighbourhood (every neighbourhood is non-empty). -/
theorem not_sum_mem_empty : ¬ (sum V₀ V₁ h₀ h₁).mem ∅ := by
  rintro (h | ⟨X, hX, h⟩ | ⟨Y, hY, h⟩)
  · exact absurd (h.symm ▸ none_mem_sumMaster) (Set.notMem_empty _)
  · obtain ⟨a, ha⟩ := inj₀_nonempty (h₀ X hX)
    exact absurd (h ▸ ha) (Set.notMem_empty _)
  · obtain ⟨b, hb⟩ := inj₁_nonempty (h₁ Y hY)
    exact absurd (h ▸ hb) (Set.notMem_empty _)

/-- On a "left" element (one reaching into the left copy), the round-trip `in₀ ∘ out₀` is the
identity. -/
theorem inMap₀_outMap₀_eq_of_left {x : (sum V₀ V₁ h₀ h₁).Element}
    (hL : ∃ X, V₀.mem X ∧ x.mem (inj₀ X)) :
    (inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap ((outMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x) = x := by
  obtain ⟨X₀, hX₀, hxX₀⟩ := hL
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, ⟨W, hxW, _, _, hLWX⟩, _, hSZ, hinjXZ⟩
    -- W ∩ inj₀ X₀ is a left copy inj₀ X₁ ⊆ Z, and lies in x
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
    · -- Z = sumMaster
      exact ⟨V₀.master, ⟨sumMaster V₀ V₁, x.master_mem, (sum V₀ V₁ h₀ h₁).master_mem,
        V₀.master_mem, (leftPart_sumMaster V₀ V₁).subset⟩, V₀.master_mem,
        (sum V₀ V₁ h₀ h₁).master_mem, inj₀_subset_sumMaster V₀.master_mem⟩
    · -- Z = inj₀ X'
      exact ⟨X', ⟨inj₀ X', hxZ, Or.inr (Or.inl ⟨X', hX', rfl⟩), hX', (leftPart_inj₀ V₀ X').subset⟩,
        hX', Or.inr (Or.inl ⟨X', hX', rfl⟩), subset_rfl⟩
    · -- Z = inj₁ Y' is impossible for a left element
      have := x.inter_mem hxX₀ hxZ
      rw [inj₀_inter_inj₁] at this
      exact absurd (x.sub this) not_sum_mem_empty

/-- On a "right" element, the round-trip `in₁ ∘ out₁` is the identity. -/
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

/-- Trichotomy for a sum-element: it reaches the left copy, or the right copy, or is `⊥`. -/
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

/-- `which(x)` selects `false` (`{1} ∈ which x`) exactly when `x` reaches into the right copy. -/
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

/-- `which(x)` selects `true` (`{0} ∈ which x`) exactly when `x` reaches into the left copy. -/
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

/-- **Exercise 3.26 (Scott 1981, PRG-19).** Scott's identity for the discriminator:
`cond(which x, in₀(out₀ x), in₁(out₁ x)) = x` for every `x ∈ |D₀ + D₁|`. -/
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
end

end DomainTheory.NeighbourhoodSystems.Exercise326
namespace DomainTheory.NeighbourhoodSystems
section

open NeighborhoodSystem ApproximableMap
variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Approximable maps are ordered by inclusion of their relations (Scott's approximation order on
`|𝒟₀ → 𝒟₁|`). Antisymmetry is `ApproximableMap.ext`. -/
instance : PartialOrder (ApproximableMap V₀ V₁) where
  le f g := ∀ X Y, f.rel X Y → g.rel X Y
  le_refl _ _ _ h := h
  le_trans _ _ _ h1 h2 X Y h := h2 X Y (h1 X Y h)
  le_antisymm f g h1 h2 := ApproximableMap.ext fun X Y => ⟨h1 X Y, h2 X Y⟩

/-- Scott's step set `[X, Y] = {f ∣ X f Y}`. -/
def step (X : Set α) (Y : Set β) : Set (ApproximableMap V₀ V₁) := {f | f.rel X Y}

@[simp] theorem mem_step {X : Set α} {Y : Set β} {f : ApproximableMap V₀ V₁} :
    f ∈ step X Y ↔ f.rel X Y := Iff.rfl

/-- A finite intersection of step sets, indexed by a list of `(X, Y)` pairs. -/
def stepFun (L : List (Set α × Set β)) : Set (ApproximableMap V₀ V₁) :=
  {f | ∀ p ∈ L, f.rel p.1 p.2}

@[simp] theorem mem_stepFun {L : List (Set α × Set β)} {f : ApproximableMap V₀ V₁} :
    f ∈ stepFun L ↔ ∀ p ∈ L, f.rel p.1 p.2 := Iff.rfl

@[simp] theorem stepFun_nil : (stepFun [] : Set (ApproximableMap V₀ V₁)) = Set.univ := by
  ext f; simp

theorem stepFun_append (L L' : List (Set α × Set β)) :
    (stepFun (L ++ L') : Set (ApproximableMap V₀ V₁)) = stepFun L ∩ stepFun L' := by
  ext f
  simp only [mem_stepFun, List.mem_append, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨hL, hL'⟩ p (hp | hp)
    · exact hL p hp
    · exact hL' p hp

theorem stepFun_cons (p : Set α × Set β) (L : List (Set α × Set β)) :
    (stepFun (p :: L) : Set (ApproximableMap V₀ V₁)) = step p.1 p.2 ∩ stepFun L := by
  ext f
  simp only [mem_stepFun, List.mem_cons, Set.mem_inter_iff, mem_step]
  constructor
  · intro h; exact ⟨h p (Or.inl rfl), fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨hp, hrest⟩ q (rfl | hq)
    · exact hp
    · exact hrest q hq

theorem stepFun_singleton (X : Set α) (Y : Set β) :
    (stepFun [(X, Y)] : Set (ApproximableMap V₀ V₁)) = step X Y := by
  rw [stepFun_cons, stepFun_nil, Set.inter_univ]

@[simp] theorem step_master_eq : (step V₀.master V₁.master : Set (ApproximableMap V₀ V₁)) = Set.univ := by
  ext f; simpa using f.master_rel

end
end DomainTheory.NeighbourhoodSystems
end
