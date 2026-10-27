module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_29
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Lemma_3_6

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.EmbeddingsIntoU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.EmbeddingsIntoU_more
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap Exercise326
universe u
/- concordance: source L5179 EXERCISE 8.19 closure under sum and product -/
/-- **Exercise 8.19.** If `T ⊴ E` and `E → E ⊴ E`, then `E + E ⊴ E` and `E × E ⊴ E`. -/
theorem exercise_8_19_assembly {α : Type u} {E : NeighborhoodSystem α}
    (hE : ∀ X, E.mem X → X.Nonempty) (hT : TD ⊴ E) (hArrow : funSpace E E ⊴ E) :
    sum E E hE hE ⊴ E ∧ prod E E ⊴ E :=
  ⟨sum_trianglelefteq_of hE hT hArrow, prod_trianglelefteq_of hT hArrow⟩
end

set_option linter.unusedVariables false

theorem example_819.{u} : And
  (And
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (hE : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E X → @Set.Nonempty α X),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
          DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
          And
            (@DomainTheory.NeighbourhoodSystems.Trianglelefteq (Option (Sum α α)) α
              (@DomainTheory.NeighbourhoodSystems.sum α α E E hE hE) E)
            (@DomainTheory.NeighbourhoodSystems.Trianglelefteq (Sum α α) α
              (@DomainTheory.NeighbourhoodSystems.prod α α E E) E))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
          DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq (Sum α α) α
            (@DomainTheory.NeighbourhoodSystems.prod α α E E) E))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (hE : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E X → @Set.Nonempty α X),
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
        DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (Option (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.sum α α E E hE hE) E) :=
  @And.intro
  (And
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (hE : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E X → @Set.Nonempty α X),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
          DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
          And
            (@DomainTheory.NeighbourhoodSystems.Trianglelefteq (Option (Sum α α)) α
              (@DomainTheory.NeighbourhoodSystems.sum α α E E hE hE) E)
            (@DomainTheory.NeighbourhoodSystems.Trianglelefteq (Sum α α) α
              (@DomainTheory.NeighbourhoodSystems.prod α α E E) E))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
          DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq (Sum α α) α
            (@DomainTheory.NeighbourhoodSystems.prod α α E E) E))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (hE : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E X → @Set.Nonempty α X),
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
        DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (Option (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.sum α α E E hE hE) E)
  (@And.intro
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (hE : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E X → @Set.Nonempty α X),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
          DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
          And
            (@DomainTheory.NeighbourhoodSystems.Trianglelefteq (Option (Sum α α)) α
              (@DomainTheory.NeighbourhoodSystems.sum α α E E hE hE) E)
            (@DomainTheory.NeighbourhoodSystems.Trianglelefteq (Sum α α) α
              (@DomainTheory.NeighbourhoodSystems.prod α α E E) E))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
          DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq (Sum α α) α
            (@DomainTheory.NeighbourhoodSystems.prod α α E E) E)
    @DomainTheory.NeighbourhoodSystems.exercise_8_19_assembly @DomainTheory.NeighbourhoodSystems.prod_trianglelefteq_of)
  @DomainTheory.NeighbourhoodSystems.sum_trianglelefteq_of

section
open NeighborhoodSystem ApproximableMap
universe u v

section FunSpace

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)

/-- **`b ↦ (λ_. b)`, the constant-function embedding.** `curry (proj₀ B A) : B → (A → B)` sends `b`
to the function that ignores its argument and always returns `b`. -/
noncomputable def constFunMap : ApproximableMap B (funSpace A B) := curry (proj₀ B A)

end FunSpace

section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)

/-- **`a ↦ ⟨a, ⊥⟩`.** -/
noncomputable def embedFst : ApproximableMap A (prod A B) := paired (idMap A) (constMap A B.bot)

/-- **`b ↦ ⟨⊥, b⟩`.** -/
noncomputable def embedSnd : ApproximableMap B (prod A B) := paired (constMap B A.bot) (idMap B)

end Prod

section FunSpace

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)

/-- **`φ ↦ φ(⊥)`, evaluation at the bottom.** -/
noncomputable def evalBotMap : ApproximableMap (funSpace A B) B :=
  (evalMap A B).comp (paired (idMap (funSpace A B)) (constMap (funSpace A B) A.bot))

@[simp] theorem toApproxMap_constFunMap (b : B.Element) (a : A.Element) :
    (toApproxMap ((constFunMap A B).toElementMap b)).toElementMap a = b := by
  rw [constFunMap, toElementMap_curry_apply, toElementMap_proj₀, fst_pair]

end FunSpace

variable {α : Type u} (D : NeighborhoodSystem α)

end

section
open NeighborhoodSystem ApproximableMap
universe u v

section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)


theorem embedFst_comp_proj₀_le : (embedFst A B).comp (proj₀ A B) ≤ idMap (prod A B) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [← pair_fst_snd z]
  set x := z.fst; set y := z.snd
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_proj₀, fst_pair, embedFst,
    toElementMap_paired, toElementMap_idMap, toElementMap_constMap]
  exact pair_le_pair_iff.mpr ⟨le_refl x, B.bot_le y⟩

end Prod
end

section
open NeighborhoodSystem ApproximableMap
universe u

/-- **Multiplicity, product case.** `embedFst`/`embedSnd` (hence the two projection pairs above)
are genuinely *different maps* as soon as `D` has an element `x ≠ ⊥`: evaluating both at `x` gives
`⟨x, ⊥⟩` vs. `⟨⊥, x⟩`, which differ in their first coordinate (`fst_pair`). -/
theorem embedFst_ne_embedSnd_of_ne_bot {α : Type u} {D : NeighborhoodSystem α} {x : D.Element}
    (hx : x ≠ D.bot) : embedFst D D ≠ embedSnd D D := fun h => hx <| by
  have heq := congrArg (fun f => f.toElementMap x) h
  simp only [embedFst, embedSnd, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap] at heq
  simpa using congrArg (·.fst) heq
end

section
open NeighborhoodSystem ApproximableMap
universe u v

section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)


theorem embedSnd_comp_proj₁_le : (embedSnd A B).comp (proj₁ A B) ≤ idMap (prod A B) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [← pair_fst_snd z]
  set x := z.fst; set y := z.snd
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_proj₁, snd_pair, embedSnd,
    toElementMap_paired, toElementMap_idMap, toElementMap_constMap]
  exact pair_le_pair_iff.mpr ⟨A.bot_le x, le_refl y⟩

theorem proj₀_comp_embedFst : (proj₀ A B).comp (embedFst A B) = idMap A := by
  apply le_antisymm <;> rw [le_iff_toElementMap_le] <;> intro a <;>
    simp [embedFst, toElementMap_comp, toElementMap_idMap, toElementMap_paired, toElementMap_constMap,
      toElementMap_proj₀, fst_pair]

theorem proj₁_comp_embedSnd : (proj₁ A B).comp (embedSnd A B) = idMap B := by
  apply le_antisymm <;> rw [le_iff_toElementMap_le] <;> intro b <;>
    simp [embedSnd, toElementMap_comp, toElementMap_idMap, toElementMap_paired, toElementMap_constMap,
      toElementMap_proj₁, snd_pair]

end Prod

section FunSpace

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)


theorem toElementMap_evalBotMap (φ : (funSpace A B).Element) :
    (evalBotMap A B).toElementMap φ = (toApproxMap φ).toElementMap A.bot := by
  simp [evalBotMap, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap, evalMap_apply]

/-- `const_{φ(⊥)} ≤ φ` pointwise, since `φ(⊥) ≤ φ(x)` for every `x` (monotonicity,
`toElementMap_mono`, Proposition 2.2(iii), applied to `⊥ ≤ x`). -/
theorem constFunMap_comp_evalBotMap_le :
    (constFunMap A B).comp (evalBotMap A B) ≤ idMap (funSpace A B) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_comp, toElementMap_idMap]
  apply (funSpaceEquiv A B).map_rel_iff.mp
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, le_iff_toElementMap_le]
  intro a
  rw [toApproxMap_constFunMap, toElementMap_evalBotMap]
  exact toElementMap_mono (toApproxMap φ) (A.bot_le a)

theorem evalBotMap_comp_constFunMap : (evalBotMap A B).comp (constFunMap A B) = idMap B := by
  apply le_antisymm <;> rw [le_iff_toElementMap_le] <;> intro b <;>
    rw [toElementMap_comp, toElementMap_idMap, toElementMap_evalBotMap, toApproxMap_constFunMap]

/-- **`B ⊴ funSpace A B`**, via `b ↦ (λ_. b)` / evaluation at `⊥`. -/
theorem trianglelefteq_funSpace_const : B ⊴ funSpace A B :=
  trianglelefteq_of_projectionPair (constFunMap A B) (evalBotMap A B)
    (evalBotMap_comp_constFunMap A B) (constFunMap_comp_evalBotMap_le A B)

end FunSpace

end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} (D : NeighborhoodSystem α)

/-- **Exercise 8.20, `D ⊴ D→D`.** -/
theorem D_trianglelefteq_funSpace : D ⊴ funSpace D D := trianglelefteq_funSpace_const D D
end

section
open NeighborhoodSystem ApproximableMap
universe u v

section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)


/-- **`A ⊴ prod A B`**, via `a ↦ ⟨a, ⊥⟩` / `proj₀`. -/
theorem trianglelefteq_prod_fst : A ⊴ prod A B :=
  trianglelefteq_of_projectionPair (embedFst A B) (proj₀ A B) (proj₀_comp_embedFst A B)
    (embedFst_comp_proj₀_le A B)

end Prod
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} (D : NeighborhoodSystem α)

/-- **Exercise 8.20, `D ⊴ D×D`.** -/
theorem D_trianglelefteq_prod : D ⊴ prod D D := trianglelefteq_prod_fst D D

end
end DomainTheory.NeighbourhoodSystems
