module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.recDomainEq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Exercise619

/-- Scott's Exercise 6.24: simultaneous subsystem solutions. -/
theorem example_624 :
    ∃ D E : ScottSys, D.sys ◁ (D.sum (D.prod E)).sys ∧ E.sys ◁ (D.sum E).sys :=
  ⟨Exercise624.Dsol, Exercise624.Esol, Exercise624.Dsol_subsystem, Exercise624.Esol_subsystem⟩

end DomainTheory.NeighbourhoodSystems
