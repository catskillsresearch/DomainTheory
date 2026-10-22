module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.interDFA_accepts

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise722

set_option linter.unusedVariables false

theorem example_722_dfa : ∀ {σ₁ σ₂ : Type} (M₁ : DFA Bool σ₁) (M₂ : DFA Bool σ₂) (a b : DomainTheory.NeighbourhoodSystems.Exercise722.SExpr),
  @Eq (Language Bool) (@DFA.accepts Bool σ₁ M₁) (DomainTheory.NeighbourhoodSystems.Exercise722.denote a) →
    @Eq (Language Bool) (@DFA.accepts Bool σ₂ M₂) (DomainTheory.NeighbourhoodSystems.Exercise722.denote b) →
      @Eq (Language Bool) (@DFA.accepts Bool (Prod σ₁ σ₂) (@DFA.inter Bool σ₁ σ₂ M₁ M₂))
        (DomainTheory.NeighbourhoodSystems.Exercise722.denote (a.cap b)) :=
  @DomainTheory.NeighbourhoodSystems.Exercise722.interDFA_accepts

end DomainTheory.NeighbourhoodSystems.Exercise722
