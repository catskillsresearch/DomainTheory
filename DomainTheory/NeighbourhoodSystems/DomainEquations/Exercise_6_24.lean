module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.recDomainEq

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open DomainTheory.NeighbourhoodSystems.FunctorTokens
/-- Scott's Exercise 6.24: simultaneous subsystem solutions. -/
theorem example_624 :
    ∃ D E : ScottSys, D.sys ◁ (D.sum (D.prod E)).sys ∧ E.sys ◁ (D.sum E).sys :=
  ⟨RecDomainEq.Dsol, RecDomainEq.Esol, RecDomainEq.Dsol_subsystem, RecDomainEq.Esol_subsystem⟩

