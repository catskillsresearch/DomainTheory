module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive













/-- **The defining equation of `Γ`, read as a theorem.** Every `γ ∈ Γ` is either `*` or `(i, γ')`
for some `i, γ'`: `Γ = (⋃ᵢ {i} × Γ) ∪ {*}`. -/
theorem Gamma_cases (γ : Gamma) : γ = star ∨ ∃ i γ', γ = cons i γ' := by
  cases γ with
  | inl l =>
    cases l with
    | nil => exact Or.inl rfl
    | cons i l' => exact Or.inr ⟨i, .inl l', rfl⟩
  | inr s =>
    refine Or.inr ⟨s 0, .inr (fun n => s (n + 1)), ?_⟩
    simp only [cons]
    congr 1
    funext n
    cases n <;> rfl

end DomainTheory.NeighbourhoodSystems.Exercise724
