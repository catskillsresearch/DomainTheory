/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Factoid33

/-!
# Factoid 4.1 — `|A|` is an inf-semilattice under intersection

**Factoid 4.1 (Scott §4 / inventory).** The intersection of two elements is again an
element, so `|A|` is an inf-semilattice under `∩`. In particular
`x ⊆ y ↔ x ∩ y = x`. Scott also records that `∩` is idempotent, commutative, and
associative, and that `⊥` is a zero for `∩`.
-/

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 4.1.** Binary meet of elements is set-theoretic intersection. -/
def inf (x y : sys.Element) : sys.Element where
  carrier := x.carrier ∩ y.carrier
  consistent := fun Y hY =>
    x.consistent Y (Set.Subset.trans hY Set.inter_subset_left)
  closed := fun Y a hY hEnt =>
    ⟨x.closed Y a (Set.Subset.trans hY Set.inter_subset_left) hEnt,
     y.closed Y a (Set.Subset.trans hY Set.inter_subset_right) hEnt⟩
end InfoSys
end DomainTheory.InformationSystems
