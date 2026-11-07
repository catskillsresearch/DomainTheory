module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.coalesceSmash

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap SeqEqB BitDom DomainTheory.NeighbourhoodSystems.SmashProduct DomainTheory.NeighbourhoodSystems.FunctorTokens

/-- Scott's Exercise 6.21: rooted grammars admit a subsystem solution and a fixed-point set containing `[]`. -/
theorem example_621 :
    (∀ (T : GExpr), T.RootedConst →
      ∃ (Γ : Set Str) (h : Γ.Nonempty),
        (singletonSys Γ h).sys ◁ (T.obj (singletonSys Γ h)).sys) ∧
    (∀ (T : GExpr), T.RootedConst → ∃ (Γ : Set Str), ([] : Str) ∈ Γ ∧ gFun T Γ = Γ) :=
  ⟨@gExists_singleton_subsystem, @gExists_tok_fixedPoint⟩

