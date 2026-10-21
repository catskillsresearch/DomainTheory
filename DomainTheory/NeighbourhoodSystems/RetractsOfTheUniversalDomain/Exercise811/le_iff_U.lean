/-ai
An element x of R lies below y if and only if every interval [0, r) belonging to x belongs to y.

The forward direction restricts the order to those intervals. Conversely, if a set belongs to x, the subproperty writes it as some [0, r), and the hypothesis puts that interval in y.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
import all Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
import all Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
import all Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import all Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.mkElement_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- Domain order reduces to a statement about `mem` at the endpoints `[0,r)` alone. -/
theorem le_iff_U {x y : R.Element} :
    x ≤ y ↔ ∀ r : ℚ, x.mem (Set.Ico 0 r) → y.mem (Set.Ico 0 r) :=
  ⟨fun h r => h (Set.Ico 0 r), fun h X hX => by
    obtain ⟨r, _, _, rfl⟩ := x.sub hX; exact h r hX⟩

end DomainTheory.NeighbourhoodSystems.Exercise811
