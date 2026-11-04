module

public import DomainTheory.DataTypesAsLattices.Closures.closureCompact
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow
import DomainTheory.DataTypesAsLattices.Closures.compact_fixed_iff
import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow_more
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

end DomainTheory.DataTypesAsLattices
