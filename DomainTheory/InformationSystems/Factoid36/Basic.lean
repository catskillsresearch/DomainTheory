/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Constructive
public import DomainTheory.InformationSystems.Factoid35

@[expose] public section

/-!
# Factoid 3.6 — every element is the directed union of its finite approximations

**Factoid 3.6 (Scott §3 / inventory).** For every element `x ∈ |A|`,
`x` equals the union of all `ū` with `u ∈ Con` and `u ⊆ x`.
Intuitively: every element is the limit of its finite approximations. The union is directed.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- The set-theoretic union of all finite approximations of `x`. -/
def approxUnion (x : sys.Element) : Set α :=
  {a | ∃ (u : Finset α) (hu : u ∈ sys.Con),
    ↑u ⊆ x.carrier ∧ a ∈ (sys.closure u hu).carrier}
end InfoSys
end DomainTheory.InformationSystems
