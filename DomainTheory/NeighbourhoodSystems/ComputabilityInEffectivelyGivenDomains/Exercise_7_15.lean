module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.iterEffective
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.coalescedSum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.smashEffective

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap DomainTheory.NeighbourhoodSystems.SmashProduct

/-- Scott's Exercise 7.15: effective givenness for iterate, coalesced sum, and smash. -/
theorem example_715 :
    (∀ {α : Type*} {V : NeighborhoodSystem α},
      V.IsEffectivelyGiven → (iterSys V).IsEffectivelyGiven) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty),
      V₀.IsEffectivelyGiven → V₁.IsEffectivelyGiven → (osum h₀ h₁).IsEffectivelyGivenS) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β},
      V₀.IsEffectivelyGiven → V₁.IsEffectivelyGiven → (smash V₀ V₁).IsEffectivelyGivenS) :=
  ⟨@iterSys_isEffectivelyGiven, ⟨@osum_isEffectivelyGivenS, @smash_isEffectivelyGivenS⟩⟩

