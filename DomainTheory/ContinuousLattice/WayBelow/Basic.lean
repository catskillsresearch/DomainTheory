/-ai
This file gathers and re-exports the core of Scott's induced topology: the predicate of being Scott-open, the way-below relation, the predicate of being a continuous lattice, and the infix notation for way-below.
ai-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.WayBelow.IsContinuousLattice
public import DomainTheory.ContinuousLattice.WayBelow.Basic.notation5

@[expose] public section

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


end DomainTheory.ContinuousLattice
