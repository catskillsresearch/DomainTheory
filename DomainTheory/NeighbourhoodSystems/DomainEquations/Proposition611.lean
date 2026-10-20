/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam
public import DomainTheory.NeighbourhoodSystems.DomainEquations.interSys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.unionSys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.ofMem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subIso
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subsystemReprIso
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_master_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_mem_E
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_inter_closed
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.interSys_subsystem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.interSys_nbset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_sInter_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.unionSys_subsystem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.unionSys_nbset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_sUnion_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611Inst16
public import DomainTheory.NeighbourhoodSystems.DomainEquations.ofMem_subsystem

@[expose] public section

/-!
# Lecture VI — Proposition 6.11 (Scott 1981, PRG-19): the subsystems of `E` form a domain

**Proposition 6.11.** For a given neighbourhood system `E`, the set of subsystems

`{D ∣ D ◁ E}`

forms a domain in its own right.

Scott derives this as a one-line corollary of the remark preceding it: *the union of a directed
family of subdomains of `E` is again a subdomain*. We make this precise using the project's
**abstract representation theorem** (Exercise 2.22, `Exercise222.reprIso`): a family `C` of sets
that is closed under (i) non-empty intersection and (ii) directed union is order-isomorphic to a
domain `|reprSystem C|` — exactly the route used for "the open sets form a domain" (Exercise 3.25)
and "the function space is a domain" (Exercise 3.27).

The faithful translation runs as follows. A subsystem `D ◁ E` is, by `NeighborhoodSystem.ext` and
the standing `D.master = E.master`, completely determined by its **family of neighbourhoods**
`{X ∣ D.mem X}`. So we represent the poset `({D ∣ D ◁ E}, ◁)` by the family

`subFam E = { {X ∣ D.mem X} ∣ D ◁ E } ⊆ 𝒫(𝒫(Δ))`,

ordered by `⊆`. By Scott's remark (`Subsystem.subsystem_iff_subset_of_common`) the subdomain
relation `◁` between two subsystems of `E` is just inclusion of their neighbourhood families, so
`({D ∣ D ◁ E}, ◁) ≃o (subFam E, ⊆)` (`subIso`). The two closure properties hold:

* **non-empty intersections** (`subFam_sInter_mem`): the intersection of a non-empty family of
  subdomains is the subdomain `interSys` whose neighbourhoods are the common neighbourhoods;
* **directed unions** (`subFam_sUnion_mem`): the union of a directed family of subdomains is the
  subdomain `unionSys` (Scott's remark) — directedness is used exactly to verify closure under
  consistent intersection.

The capstone `subsystemReprIso : {D ∣ D ◁ E} ≃o |reprSystem (subFam E) …|` composes `subIso` with
`Exercise222.reprIso`, witnessing that the subsystems of `E` *are* (isomorphic to) a domain.

**Axioms.** The combinatorial heart — `subFam` and its closure under intersection/union, the
subsystem constructions `interSys`/`unionSys`, and `subIso` — is **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`). The final `subsystemReprIso` inherits `Classical.choice`
solely through Exercise 2.22's representation isomorphism (the "for set theorists" exercise, which
picks witnesses of non-emptiness and uses finite-set induction), exactly as Exercise 3.27 does.
-/

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-! ### The representing family of neighbourhood-sets. -/






/-! ### Closure under non-empty intersection. -/





/-! ### Closure under directed union (Scott's remark). -/





/-! ### The poset of subsystems and its representation. -/






end DomainTheory.NeighbourhoodSystems.Proposition611
