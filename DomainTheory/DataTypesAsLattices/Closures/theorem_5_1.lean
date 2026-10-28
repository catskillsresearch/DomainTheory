module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.DirectedSubset
public import DomainTheory.DataTypesAsLattices.Retracts.IsCompactSubset
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.Isolated
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow
public import DomainTheory.DataTypesAsLattices.Closures.compact_fixed_iff
public import DomainTheory.DataTypesAsLattices.Retracts.vals
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow_more
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_5_1 {a : Pomega} (ha : Closure a) :
    (∀ x : Fixpoints (funOf a),
      IsCompactSubset x ↔ ∃ n, x = closureCompact a ha n) ∧
    ∀ x : Fixpoints (funOf a),
      DirectedSubset (compactFixedBelow a x) ∧
        (x : Pomega) = ⋃₀ (Subtype.val '' compactFixedBelow a x) :=
  ⟨compact_fixed_iff.subset ha, fun x =>
    ⟨compactFixedBelow.directedSubset ha x, compactFixedBelow.sUnion ha x⟩⟩

theorem theorem_5_1.isolated {a : Pomega} (_ha : Closure a) {x : Pomega}
    (hx : typed x a) :
    Isolated x → ∃ n, x = funOf a (e n) := by
  intro h
  obtain ⟨n, hn⟩ := h.out
  refine ⟨n, ?_⟩
  rw [hn] at hx ⊢
  exact hx

end DomainTheory.DataTypesAsLattices
