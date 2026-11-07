module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.coalesceSmash

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB SmashProduct Exercise619

/-- Scott's Exercise 6.21: rooted grammars admit a subsystem solution and a fixed-point set containing `[]`. -/
theorem example_621 :
    (∀ (T : GExpr), T.RootedConst →
      ∃ (Γ : Set Str) (h : Γ.Nonempty),
        (singletonSys Γ h).sys ◁ (T.obj (singletonSys Γ h)).sys) ∧
    (∀ (T : GExpr), T.RootedConst → ∃ (Γ : Set Str), ([] : Str) ∈ Γ ∧ gFun T Γ = Γ) :=
  ⟨@gExists_singleton_subsystem, @gExists_tok_fixedPoint⟩

end DomainTheory.NeighbourhoodSystems
