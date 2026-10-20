/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module


public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace Exercise619

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

/-- **An object of the Exercise 6.19 category.** An `∅`-free neighbourhood system over
`Str = {0,1}*` (`ne`: every neighbourhood is non-empty, Scott's `∅ ∉ 𝒟`). -/
structure ScottSys where
  /-- The underlying neighbourhood system on `{0,1}*`. -/
  sys : NeighborhoodSystem Str
  /-- `∅ ∉ 𝒟`: every neighbourhood is non-empty. -/
  ne : ∀ X, sys.mem X → X.Nonempty

end Exercise619
end DomainTheory.NeighbourhoodSystems
