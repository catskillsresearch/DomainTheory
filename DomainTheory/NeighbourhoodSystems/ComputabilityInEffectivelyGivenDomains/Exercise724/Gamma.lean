/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- Scott's set `Γ`, the *terminal* solution of `Γ = (⋃ᵢ {i} × Γ) ∪ {*}`: a finite sequence,
terminating at `*` (`Sum.inl`), or an infinite one that never terminates (`Sum.inr`). -/
abbrev Gamma : Type := List ℕ ⊕ (ℕ → ℕ)

end DomainTheory.NeighbourhoodSystems.Exercise724
