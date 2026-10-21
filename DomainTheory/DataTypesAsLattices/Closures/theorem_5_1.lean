/-ai
Scott's algebraic lattice theorem says that, for a closure, a fixed point is compact exactly when it is the value of the closure on some finite set, and every fixed point is the directed supremum of the compact fixed points below it.

The compactness criterion is the previously proved characterization of compact fixed points, and the directed supremum is the previously proved directedness of the compact fixed points below a fixed point together with the decomposition of the fixed point as their union.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow_directedSubset
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow_sUnion
public import DomainTheory.DataTypesAsLattices.Closures.compact_fixed_iff_subset

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


















/-- **Scott 1976, Theorem 5.1 (The algebraic lattice theorem).**
The compact points of a closure range are exactly the `a(e n)`, and every
fixed point is their directed supremum. -/
theorem theorem_5_1 {a : Pomega} (ha : IsClosure a) :
    (∀ x : Fixpoints (funOf a),
      IsCompactSubset x ↔ ∃ n, x = closureCompact a ha n) ∧
    ∀ x : Fixpoints (funOf a),
      IsDirectedSubset (compactFixedBelow a x) ∧
        (x : Pomega) = ⋃₀ (Subtype.val '' compactFixedBelow a x) :=
  ⟨compact_fixed_iff_subset ha, fun x =>
    ⟨compactFixedBelow_directedSubset ha x, compactFixedBelow_sUnion ha x⟩⟩

end DomainTheory.DataTypesAsLattices
