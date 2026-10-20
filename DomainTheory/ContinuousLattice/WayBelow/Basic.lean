/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed

/-!
# The induced (Scott) topology and the way-below relation (Scott 1972, §2)

This file formalizes the core of Scott's §2 *Continuous Lattices*: the topology a complete
lattice carries intrinsically (Scott's "induced topology", today the **Scott topology**),
the **way-below relation** `≪`, the basic properties of `≪` (Scott's Proposition 2.2), and
the definition of a **continuous lattice** (Scott's Definition 2.3).

Scott defines the induced topology on a partially ordered set `D` by declaring `U` open iff

* (i)  `U` is an upper set; and
* (ii) whenever `S ⊆ D` is directed (and, in this paper, non-empty), `⊔S` exists and
       `⊔S ∈ U`, then `S ∩ U ≠ ∅`.

He then defines `x ≪ y` ("`x` is way below `y`") to mean `y ∈ interior {z | x ⊑ z}`, the
interior being taken in this induced topology. We encode "Scott-open" as the predicate
`ScottOpen` and `≪` as `WayBelow`, witnessing the interior by a Scott-open neighbourhood
contained in the principal up-set `Set.Ici x = {z | x ≤ z}`. This is faithful to Scott's
topological definition (rather than the order-theoretic shortcut), and as a result Scott's
Proposition 2.2 (vi) and (vii) fall straight out of the open-set axioms.

This is the classical/topological version of the theory, so we reason classically.
-/

namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]

/-- **Scott 1972, §2, the induced topology.** `U` is *Scott-open* when it is an upper set and
is inaccessible by suprema of non-empty directed sets: if a non-empty directed `S` has its
supremum in `U`, then some member of `S` already lies in `U`. -/
def ScottOpen (U : Set D) : Prop :=
  letI : LE D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
  letI : SupSet D :=
    (CompleteLattice.toCompleteSemilatticeSup (α := D)).toSupSet
  IsUpperSet U ∧
    ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → sSup S ∈ U → (S ∩ U).Nonempty

/-- **Scott 1972, §2.** The *way-below* relation: `x ≪ y` iff `y` lies in the interior of the
principal up-set `Set.Ici x` for the induced topology, witnessed by a Scott-open
neighbourhood of `y` contained in `Set.Ici x`. -/
def WayBelow (x y : D) : Prop :=
  letI : LE D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
  letI : Preorder D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder
  ∃ U : Set D, ScottOpen U ∧ y ∈ U ∧ U ⊆ Set.Ici x

@[inherit_doc] scoped infix:50 " ≪ " => WayBelow

/-- **Scott 1972, Definition 2.3.** A complete lattice `D` is a *continuous lattice* when every
element is the supremum of the elements way below it: `y = ⊔ {x | x ≪ y}`. -/
def IsContinuousLattice (D : Type u) [CompleteLattice D] : Prop :=
  letI : LE D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
  ∀ y : D, IsLUB {x | x ≪ y} y
end DomainTheory.ContinuousLattice
