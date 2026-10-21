/-ai
The concatenation automaton accepts exactly the concatenation of the two accepted languages.

The numbered name example_722_cat is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat.catEps_accepts

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise722

set_option linter.unusedVariables false

theorem example_722_cat : ∀ {σ₁ σ₂ : Type} (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂),
  @Eq (Language Bool)
    (@εNFA.accepts Bool (Sum σ₁ σ₂) (@DomainTheory.NeighbourhoodSystems.Exercise722.catEps σ₁ σ₂ M₁ M₂))
    (DomainTheory.NeighbourhoodSystems.Exercise722.concat (@NFA.accepts Bool σ₁ M₁) (@NFA.accepts Bool σ₂ M₂)) :=
  @DomainTheory.NeighbourhoodSystems.Exercise722.catEps_accepts

end DomainTheory.NeighbourhoodSystems.Exercise722
