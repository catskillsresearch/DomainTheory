module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.intExprDomains

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open DomainTheory.NeighbourhoodSystems.FunctorTokens BitDom

/-- Scott's Exercise 6.22: an N★ solution over a rooted N. -/
theorem example_622 :
    ∃ N : ScottSys, ([] : Str) ∈ N.sys.master ∧
      ∃ (Γ : Set Str) (h : Γ.Nonempty),
        (singletonSys Γ h).sys ◁ ((NStarExpr N).obj (singletonSys Γ h)).sys :=
  @NStar_over_N_exists

