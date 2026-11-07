module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumProdTok

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap BitDom Exercise619

/-- Scott's Exercise 6.19: product and sum token neighbourhood systems are isomorphic to `prod` and `sum`. -/
theorem example_619 :
    (∀ {D₀ D₁ : NeighborhoodSystem Str}, prodTok D₀ D₁ ≅ᴰ prod D₀ D₁) ∧
    (∀ {D₀ D₁ : NeighborhoodSystem Str} {h₀ : ∀ X, D₀.mem X → X.Nonempty}
        {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty},
      sumTok D₀ D₁ h₀ h₁ ≅ᴰ sum D₀ D₁ h₀ h₁) :=
  ⟨@prodTok_iso_prod, @sumTok_iso_sum⟩

end DomainTheory.NeighbourhoodSystems
