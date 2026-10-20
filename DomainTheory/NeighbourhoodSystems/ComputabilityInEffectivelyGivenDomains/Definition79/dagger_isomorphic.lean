/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Definition 7.9 — `𝒟 ≅ 𝒟†` (Exercise 1.20).** The preparation does not change the domain:
`𝒟` and `𝒟†` are isomorphic. (This is what makes `ℙ𝒟` isomorphism-invariant.) -/
theorem dagger_isomorphic : V ≅ᴰ V.dagger := V.isomorphic_powerSystem

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
