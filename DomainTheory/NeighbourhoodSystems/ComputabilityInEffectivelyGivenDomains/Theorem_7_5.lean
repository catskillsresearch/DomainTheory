module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.funPresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap

/-- Scott's Theorem 7.5: function space effective givenness and computability. -/
theorem theorem_75 :
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) (gN : ℕ → ℕ),
      Nat.Primrec gN →
        (∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
          : Set (ApproximableMap V₀ V₁)).Nonempty) →
          ∀ (φ : (funSpace V₀ V₁).Element),
            REPred (fun c => φ.mem (Xenum P₀ P₁ gN c)) ↔
              ComputableMap P₀ P₁ (toApproxMap φ)) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β},
      V₀.IsEffectivelyGiven → V₁.IsEffectivelyGiven → (funSpace V₀ V₁).IsEffectivelyGiven) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
      {V₂ : NeighborhoodSystem γ} (P₂ : ComputablePresentation V₂)
      (gN incl0 incl1 eq1 : ℕ → ℕ)
      (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₁ P₂ (decodeList c))
        : Set (ApproximableMap V₁ V₂)).Nonempty) (hgNp : Nat.Primrec gN)
      (hincl0 : ∀ s, incl0 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) (hincl0p : Nat.Primrec incl0)
      (hincl1 : ∀ s, incl1 s = 1 ↔ P₂.X s.unpair.1 ⊆ P₂.X s.unpair.2) (hincl1p : Nat.Primrec incl1)
      (heq1 : ∀ s, eq1 s = 1 ↔ P₂.X s.unpair.1 = P₂.X s.unpair.2) (heq1p : Nat.Primrec eq1)
      {g : ApproximableMap (prod V₀ V₁) V₂},
      ComputableMap (prodPresentation P₀ P₁) P₂ g →
        ComputableMap P₀ (funPresentation P₁ P₂ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
          hincl1 hincl1p heq1 heq1p) (curry g)) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
      (gN incl0 incl1 eq1 : ℕ → ℕ)
      (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
        : Set (ApproximableMap V₀ V₁)).Nonempty) (hgNp : Nat.Primrec gN)
      (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) (hincl0p : Nat.Primrec incl0)
      (hincl1 : ∀ s, incl1 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) (hincl1p : Nat.Primrec incl1)
      (heq1 : ∀ s, eq1 s = 1 ↔ P₁.X s.unpair.1 = P₁.X s.unpair.2) (heq1p : Nat.Primrec eq1),
      ComputableMap
        (prodPresentation (funPresentation P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
          hincl1 hincl1p heq1 heq1p) P₀) P₁ (evalMap V₀ V₁)) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
      (gN incl0 incl1 eq1 : ℕ → ℕ)
      (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
        : Set (ApproximableMap V₀ V₁)).Nonempty) (hgNp : Nat.Primrec gN)
      (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) (hincl0p : Nat.Primrec incl0)
      (hincl1 : ∀ s, incl1 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) (hincl1p : Nat.Primrec incl1)
      (heq1 : ∀ s, eq1 s = 1 ↔ P₁.X s.unpair.1 = P₁.X s.unpair.2) (heq1p : Nat.Primrec eq1)
      (φ : (funSpace V₀ V₁).Element),
      ComputableElement (funPresentation P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
          hincl1 hincl1p heq1 heq1p) φ ↔ ComputableMap P₀ P₁ (toApproxMap φ)) :=
  ⟨@Xenum_isComputableElement_iff, ⟨@funSpace_isEffectivelyGiven, ⟨@curry_isComputable,
    ⟨@evalMap_isComputable, @isComputableElement_funPresentation_iff⟩⟩⟩⟩

end DomainTheory.NeighbourhoodSystems
