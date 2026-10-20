module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Dsol_subsystem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Esol_subsystem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624

















/-- **Exercise 6.24 (object level).** By the double fixed-point method there exist `∅`-free systems
`D`, `E` over `{0,1}*` such that `{D} ◁ D + (D×E)` and `{E} ◁ D + E` **simultaneously**. These two
facts are exactly the joint hypothesis of the simultaneous Theorem 6.14, which then yields the
required isomorphisms `D ≅ D + (D×E)` and `E ≅ D + E`. -/
theorem exists_simultaneous_subsystems :
    ∃ D E : ScottSys, D.sys ◁ (D.sum (D.prod E)).sys ∧ E.sys ◁ (D.sum E).sys :=
  ⟨Dsol, Esol, Dsol_subsystem, Esol_subsystem⟩

end Exercise624
end DomainTheory.NeighbourhoodSystems
