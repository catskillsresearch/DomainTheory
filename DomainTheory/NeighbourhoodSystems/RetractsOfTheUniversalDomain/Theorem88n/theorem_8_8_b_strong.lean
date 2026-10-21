/-ai
Theorem 8.8(b), strengthened. For any effectively given neighbourhood system there is a computable projection pair directly into the universal domain and back.

Let the subsystem be the coded copy inside the universal domain. Take the composite of its injection after the code-level injection, and the composite of the code-level projection after its projection. The round trip on the system is the identity by associativity, the subsystem law that projection after injection is the identity, cancellation of an identity composite, and the code-level round trip. The other composite equals the subsystem's injection after its projection, by associativity, the code-level round trip on the copy, and cancellation of an identity composite, hence lies below the identity on the universal domain. Computability of the two composites is composition of the computability of the code-level injection with that of the subsystem injection, and of the computability of the subsystem projection with that of the code-level projection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_inj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_proj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_projectionPair_isComputable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88n.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88n.isoProj_comp_isoInj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88n.isoInj_comp_isoProj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88n.isoInj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88n.isoProj_isComputableMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)







/-- **`theorem_8_8_b`, strengthened.** For any effectively given `D` (via `P`), there is a
*single* computable projection pair `i : D → U`, `j : U → D` directly (no intermediate isomorphic
copy): compose `isoInj`/`isoProj` (the code-level iso, computable) with `DprimeUCode`'s own projection pair
into `U` (Theorem 8.8(b)(vii), computable). -/
theorem theorem_8_8_b_strong :
    ∃ (i : ApproximableMap D U) (j : ApproximableMap U D),
      j.comp i = idMap D ∧ i.comp j ≤ idMap U ∧
        IsComputableMap P UComputablePresentation i ∧
        IsComputableMap UComputablePresentation P j := by
  set h := DprimeUCode_subsystem P with hh
  refine ⟨h.inj.comp (isoInj P), (isoProj P).comp h.proj, ?_, ?_, ?_, ?_⟩
  · rw [comp_assoc, ← comp_assoc h.proj h.inj (isoInj P), h.proj_comp_inj, idMap_comp]
    exact isoProj_comp_isoInj P
  · have heq : (h.inj.comp (isoInj P)).comp ((isoProj P).comp h.proj) = h.inj.comp h.proj := by
      rw [comp_assoc, ← comp_assoc (isoInj P) (isoProj P) h.proj, isoInj_comp_isoProj, idMap_comp]
    rw [heq]
    exact h.inj_comp_proj_le
  · exact comp_isComputable (isoInj_isComputableMap P) (DprimeUCode_inj_isComputableMap P)
  · exact comp_isComputable (DprimeUCode_proj_isComputableMap P) (isoProj_isComputableMap P)

end DomainTheory.NeighbourhoodSystems
