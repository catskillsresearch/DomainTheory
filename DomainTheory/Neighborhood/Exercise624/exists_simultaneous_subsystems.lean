/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise619PartB
public import DomainTheory.Neighborhood.Exercise624.Basic
public import DomainTheory.Neighborhood.Exercise624.Dsol_subsystem
public import DomainTheory.Neighborhood.Exercise624.Esol_subsystem

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB

namespace Exercise624

















/-- **Exercise 6.24 (object level).** By the double fixed-point method there exist `∅`-free systems
`D`, `E` over `{0,1}*` such that `{D} ◁ D + (D×E)` and `{E} ◁ D + E` **simultaneously**. These two
facts are exactly the joint hypothesis of the simultaneous Theorem 6.14, which then yields the
required isomorphisms `D ≅ D + (D×E)` and `E ≅ D + E`. -/
theorem exists_simultaneous_subsystems :
    ∃ D E : ScottSys, D.sys ◁ (D.sum (D.prod E)).sys ∧ E.sys ◁ (D.sum E).sys :=
  ⟨Dsol, Esol, Dsol_subsystem, Esol_subsystem⟩

end Exercise624
end DomainTheory.Neighborhood
