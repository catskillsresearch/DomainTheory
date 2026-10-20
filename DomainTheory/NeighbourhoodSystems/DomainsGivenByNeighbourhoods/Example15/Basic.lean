/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Fintype.Powerset
import all Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4Mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.neighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4_master_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4_master_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4_inter_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4_sub_master

@[expose] public section

/-!
# Example 1.5 (Scott 1981, PRG-19, §1)

Scott's fourth worked example: tokens `Δ = {0, 1, 2, 3}` and `𝒟` the family of **all non-empty
subsets** of `Δ`.

> This system is a direct generalization of Example 1.2 … The verification that the present `𝒟`
> is a neighbourhood system rests on nothing more than the remark that sets are consistent in `𝒟`
> iff they have a non-empty intersection.

We encode tokens as `Fin 4`, take `mem X := X.Nonempty`, and `master := Set.univ`. Condition (ii)
of Definition 1.1 is immediate: a consistency witness `Z ⊆ X ∩ Y` that is itself non-empty makes
`X ∩ Y` non-empty.

* **Example 1.5** — `neighborhoodSystem`.
* **Factoid 1.5a** — `consistent_iff_inter_nonempty`: a finite prefix is consistent in `𝒟` iff its
  intersection is non-empty (Scott's "remark").

Unlike Examples 1.2–1.4 this construction needs no `fin_cases`/`decide`: it is `Set.Nonempty`
bookkeeping, so it audits **constructive** (`[propext, Quot.sound]`).
-/

namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem









/-- The neighbourhoods of Example 1.5 are a finite family, hence countable. -/
instance P4_countable : Countable {S : Set Token // neighborhoodSystem.mem S} :=
  inferInstance
end DomainTheory.NeighbourhoodSystems.Example15
