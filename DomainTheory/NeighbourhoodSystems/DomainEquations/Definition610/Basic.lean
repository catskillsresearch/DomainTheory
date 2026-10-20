/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610.Subsystem

@[expose] public section

/-!
# Lecture VI — Definition 6.10 (Scott 1981, PRG-19): the subsystem relation `D ◁ E`

To explain why the *minimal* solutions of a domain equation exist, Scott introduces a notion of
"subdomain". The functors `T` he has in mind are not merely continuous on maps (Definition 6.8) but
also possess continuity properties *on domains*, and those are phrased in terms of this relation.

**Definition 6.10.** For two neighbourhood systems `D` and `E` over the *same* set of tokens `Δ`,
we write `D ◁ E` to mean that
* `D ⊆ E` (every neighbourhood of `D` is a neighbourhood of `E`), **and**
* whenever `X, Y ∈ D` and `X ∩ Y ∈ E`, then `X ∩ Y ∈ D`.

The second clause is the crucial one: it says the notion of *consistency* in `D` is the **same** as
in `E`. A subdomain is a smaller family of neighbourhoods, but it must agree with `E` about which
pairs are consistent.

This module formalizes the relation together with the elementary facts Scott records in the prose:

* it is reflexive (`Subsystem.refl`) and transitive (`Subsystem.trans`);
* it is antisymmetric (`Subsystem.antisymm`): `D ◁ E` and `E ◁ D` force `D = E`;
* **Scott's remark.** If `D₀ ◁ E` and `D₁ ◁ E`, then `D₀ ◁ D₁ ↔ D₀ ⊆ D₁`
  (`Subsystem.subsystem_iff_subset_of_common`) — once both sit inside a common `E`, the
  subdomain relation collapses to plain inclusion of neighbourhood families.

Everything here is at the `Prop` level and **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
Propositions 6.11 (the subsystems of `E` form a domain) and 6.12 (a `D ◁ E` yields a projection
pair `i, j`) build on this relation and are formalized separately.
-/

namespace DomainTheory.NeighbourhoodSystems

variable {α : Type*}


@[inherit_doc] infix:50 " ◁ " => Subsystem

namespace Subsystem
end Subsystem
end DomainTheory.NeighbourhoodSystems
