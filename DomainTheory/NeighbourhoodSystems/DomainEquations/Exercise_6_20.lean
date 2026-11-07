module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.functorTokens

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap BitDom DomainTheory.NeighbourhoodSystems.FunctorTokens

/-- Scott's Exercise 6.20: `λΓ. tok(T({Γ}))` is continuous, hence a fixed point exists. -/
theorem example_620 :
    (∀ (T : FExpr), T.RootedConst → ∃ (Γ : Set Str), ([] : Str) ∈ Γ ∧ mFun T Γ = Γ) ∧
    (∀ (T : FExpr), T.RootedConst →
      ∃ (Γ : Set Str) (h : Γ.Nonempty),
        (singletonSys Γ h).sys ◁ (T.obj (singletonSys Γ h)).sys) :=
  ⟨@exists_tok_fixedPoint, @exists_singleton_subsystem⟩

