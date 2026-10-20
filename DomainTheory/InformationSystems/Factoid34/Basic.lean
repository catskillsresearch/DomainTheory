/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InfoSys

@[expose] public section

/-!
# Factoid 3.4 — top element and total elements

**Factoid 3.4 (inventory / Scott §3).** There need be no top element `⊤`. Such an
element exists if and only if every finite subset of the token set is consistent, in
which case `⊤ = D` as a set. When it exists, it is the unique *total* (maximal)
element of the domain.
-/

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- A **total** element is a maximal element of `|A|` under inclusion. -/
def IsTotal (x : sys.Element) : Prop := ∀ y, x ≤ y → y ≤ x

/-- Every finite set of tokens is consistent. -/
def AllConsistent : Prop := ∀ u : Finset α, u ∈ sys.Con

/-- **Factoid 3.4.** When every finite set is consistent, the top element is `D` itself. -/
def topElement (h : sys.AllConsistent) : sys.Element where
  carrier := Set.univ
  consistent := fun Y _ => h Y
  closed := fun _ _ _ _ => trivial
end InfoSys
end DomainTheory.InformationSystems
