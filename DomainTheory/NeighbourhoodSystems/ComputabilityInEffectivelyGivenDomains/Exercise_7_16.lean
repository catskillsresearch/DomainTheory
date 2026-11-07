module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.curryEnum

@[expose] public section

open DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false
open NeighborhoodSystem Domain.Recursive ApproximableMap

/-- Scott's Exercise 7.16: curry combination is computable with a decidable relation. -/
theorem example_716 :
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ}
      (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
      (P₂ : ComputablePresentation V₂),
      ∃ (PA : ComputablePresentation (funSpace (prod V₀ V₁) V₂))
        (PB : ComputablePresentation (funSpace V₀ (funSpace V₁ V₂))),
        RecDecidable₂ (fun n m => (curryC V₀ V₁ V₂).rel (PA.X n) (PB.X m)) ∧
          ComputableMap PA PB (curryC V₀ V₁ V₂)) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ}
      {G : Set (ApproximableMap (prod V₀ V₁) V₂)}
      {H : Set (ApproximableMap V₀ (funSpace V₁ V₂))},
      (curryC V₀ V₁ V₂).rel G H ↔ (funSpace (prod V₀ V₁) V₂).mem G ∧
        (funSpace V₀ (funSpace V₁ V₂)).mem H ∧ ∀ g ∈ G, curry g ∈ H) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ}
      (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
      (P₂ : ComputablePresentation V₂) (gNa gNb gNc : ℕ → ℕ)
      (PA : ComputablePresentation (funSpace (prod V₀ V₁) V₂))
      (PB : ComputablePresentation (funSpace V₀ (funSpace V₁ V₂)))
      (Pc : ComputablePresentation (funSpace V₁ V₂))
      (hPAX : PA.X = Xenum (prodPresentation P₀ P₁) P₂ gNa)
      (hPBX : PB.X = Xenum P₀ Pc gNb) (hPcX : Pc.X = Xenum P₁ P₂ gNc)
      (hgNa : ∀ c, gNa c = 1 ↔ (stepFun (funListOf (prodPresentation P₀ P₁) P₂ (decodeList c))
        : Set (ApproximableMap (prod V₀ V₁) V₂)).Nonempty)
      (hgNc : ∀ c, gNc c = 1 ↔ (stepFun (funListOf P₁ P₂ (decodeList c))
        : Set (ApproximableMap V₁ V₂)).Nonempty)
      (hgNbp : Nat.Primrec gNb) (hgNcp : Nat.Primrec gNc),
      RecDecidable₂ (fun n m => (curryC V₀ V₁ V₂).rel (PA.X n) (PB.X m))) :=
  ⟨@curryComb_isComputable, ⟨@curryComb_rel, @curryComb_rel_recDecidable⟩⟩

