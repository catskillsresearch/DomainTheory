module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}








open Exercise510



section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)



variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}









variable {h₀ h₁}







variable (P₀ P₁)



section CoalescedFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
  (h₀' : ∀ X, V₀'.mem X → X.Nonempty) (h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty)




/-- **`f ⊕ g` is computable.** The relation `(osumEnum n) (f⊕g) (osumEnum' m)` decodes by tags: `m`
improper (master absorbs), or `m`/`n` both proper left copies with `f`'s r.e. relation, or both
proper right copies with `g`'s. -/
theorem osumMap_isComputable (P₀' : ComputablePresentation V₀') (P₁' : ComputablePresentation V₁')
    {f : ApproximableMap V₀ V₀'} {g : ApproximableMap V₁ V₁'}
    (hf : IsComputableMapS P₀.toScott P₀'.toScott f)
    (hg : IsComputableMapS P₁.toScott P₁'.toScott g) :
    IsComputableMapS (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁))
      (osumPresentation h₀' h₁' (P₀ := P₀') (P₁ := P₁')) (osumMap h₀' h₁' f g) := by
  have mT0 : RecDecidable (fun t => t.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have mT1 : RecDecidable (fun t => t.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have mP0 : RecDecidable (fun t => P₀'.X t.unpair.2.unpair.2 ≠ V₀'.master) :=
    (proper₀_dec P₀').comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have mP1 : RecDecidable (fun t => P₁'.X t.unpair.2.unpair.2 ≠ V₁'.master) :=
    (proper₁_dec P₁').comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have nT0 : RecDecidable (fun t => t.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have nT1 : RecDecidable (fun t => t.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  have nP0 : RecDecidable (fun t => P₀.X t.unpair.1.unpair.2 ≠ V₀.master) :=
    (proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.left)
  have nP1 : RecDecidable (fun t => P₁.X t.unpair.1.unpair.2 ≠ V₁.master) :=
    (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.left)
  have Hf : REPred (fun t => f.rel (P₀.toScott.X t.unpair.1.unpair.2)
      (P₀'.toScott.X t.unpair.2.unpair.2)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hf.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right)))
  have Hg : REPred (fun t => g.rel (P₁.toScott.X t.unpair.1.unpair.2)
      (P₁'.toScott.X t.unpair.2.unpair.2)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hg.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hImp : RecDecidable (fun t => ¬(t.unpair.2.unpair.1 = 0 ∧ P₀'.X t.unpair.2.unpair.2 ≠ V₀'.master)
      ∧ ¬(t.unpair.2.unpair.1 = 1 ∧ P₁'.X t.unpair.2.unpair.2 ≠ V₁'.master)) :=
    (mT0.and mP0).not.and (mT1.and mP1).not
  refine REPred.of_iff (fun t => ?_)
    ((hImp.re).or ((((mT0.and mP0).and (nT0.and nP0)).re.and Hf).or
      (((mT1.and mP1).and (nT1.and nP1)).re.and Hg)))
  show (osumMap h₀' h₁' f g).rel (osumEnum P₀ P₁ t.unpair.1) (osumEnum P₀' P₁' t.unpair.2) ↔ _
  by_cases hm0 : t.unpair.2.unpair.1 = 0 ∧ P₀'.X t.unpair.2.unpair.2 ≠ V₀'.master
  · rw [osumEnum_left hm0]
    constructor
    · rintro ⟨-, -, hd⟩
      rcases hd with hmaster | ⟨X, Y', hnX, hW'eq, -, hf⟩ | ⟨Y, Y', -, hW'eq, -, -⟩
      · exact absurd hmaster inj₀_ne_sumMaster
      · obtain rfl : Y' = P₀'.X t.unpair.2.unpair.2 := (inj₀_injective hW'eq).symm
        by_cases hn0 : t.unpair.1.unpair.1 = 0 ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master
        · rw [osumEnum_left hn0] at hnX
          obtain rfl : P₀.X t.unpair.1.unpair.2 = X := inj₀_injective hnX
          exact Or.inr (Or.inl ⟨⟨hm0, hn0⟩, hf⟩)
        · exfalso
          by_cases hn1 : t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
          · rw [osumEnum_right hn1] at hnX
            obtain ⟨b, hb⟩ := h₁ _ (P₁.mem_X _)
            exact ir_mem_inj₀ (hnX ▸ ir_mem_inj₁.mpr hb)
          · rw [osumEnum_master hn0 hn1] at hnX
            exact none_mem_inj₀ (hnX ▸ none_mem_sumMaster)
      · obtain ⟨a, ha⟩ := h₀' _ (P₀'.mem_X _)
        exact (il_mem_inj₁ (hW'eq ▸ il_mem_inj₀.mpr ha)).elim
    · rintro (himp | ⟨⟨-, hn0⟩, hf⟩ | ⟨⟨hm1, -⟩, -⟩)
      · exact absurd hm0 himp.1
      · exact ⟨osumEnum_mem h₀ h₁ _, Or.inr (Or.inl ⟨_, P₀'.mem_X _, hm0.2, rfl⟩),
          Or.inr (Or.inl ⟨_, _, osumEnum_left hn0, rfl, hm0.2, hf⟩)⟩
      · obtain ⟨he, -⟩ := hm1; rw [hm0.1] at he; exact absurd he (by decide)
  · by_cases hm1 : t.unpair.2.unpair.1 = 1 ∧ P₁'.X t.unpair.2.unpair.2 ≠ V₁'.master
    · rw [osumEnum_right hm1]
      constructor
      · rintro ⟨-, -, hd⟩
        rcases hd with hmaster | ⟨X, Y', -, hW'eq, -, -⟩ | ⟨Y, Y', hnY, hW'eq, -, hg⟩
        · exact absurd hmaster inj₁_ne_sumMaster
        · exact absurd hW'eq.symm (inj₀_ne_inj₁_of_nonempty (h₁' _ (P₁'.mem_X _)))
        · obtain rfl : Y' = P₁'.X t.unpair.2.unpair.2 := (inj₁_injective hW'eq).symm
          by_cases hn1 : t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
          · rw [osumEnum_right hn1] at hnY
            obtain rfl : P₁.X t.unpair.1.unpair.2 = Y := inj₁_injective hnY
            exact Or.inr (Or.inr ⟨⟨hm1, hn1⟩, hg⟩)
          · exfalso
            by_cases hn0 : t.unpair.1.unpair.1 = 0 ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master
            · rw [osumEnum_left hn0] at hnY
              obtain ⟨a, ha⟩ := h₀ _ (P₀.mem_X _)
              exact il_mem_inj₁ (hnY ▸ il_mem_inj₀.mpr ha)
            · rw [osumEnum_master hn0 hn1] at hnY
              exact none_mem_inj₁ (hnY ▸ none_mem_sumMaster)
      · rintro (himp | ⟨⟨hm0', -⟩, -⟩ | ⟨⟨-, hn1⟩, hg⟩)
        · exact absurd hm1 himp.2
        · obtain ⟨he, -⟩ := hm0'; rw [hm1.1] at he; exact absurd he (by decide)
        · exact ⟨osumEnum_mem h₀ h₁ _, Or.inr (Or.inr ⟨_, P₁'.mem_X _, hm1.2, rfl⟩),
            Or.inr (Or.inr ⟨_, _, osumEnum_right hn1, rfl, hm1.2, hg⟩)⟩
    · rw [osumEnum_master hm0 hm1]
      constructor
      · intro _; exact Or.inl ⟨hm0, hm1⟩
      · intro _
        exact ⟨osumEnum_mem h₀ h₁ _, (osum h₀' h₁').master_mem, Or.inl rfl⟩

end CoalescedFunctor
end Coalesced
end DomainTheory.NeighbourhoodSystems
