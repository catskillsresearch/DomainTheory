/-ai
The code-level projection is a computable map from the presentation of the coded copy to the original presentation.

Pairing the first component of a code with the index involution of the second component is primitive recursive. Inclusion of the coded neighbourhood of the first component in the coded neighbourhood of that reindexed second component is recursively decidable by composing inclusion decidability of the coded presentation with the reindexing; after simplifying the unpairing of a pair the two sides agree by reflexivity. The recursively enumerable predicate of that decidable predicate agrees with the relation of the projection by the reduction of the relation to a single inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_inj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_proj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_projectionPair_isComputable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88n.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88n.isoProj_rel_iff_incl

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






/-- **`isoProj` is computable** relative to `DprimeUCodePresentation P`/`P`: its raw-index relation is
`DprimeUCodePresentation`'s `incl_computable` reindexed by `eIdx P` in the second argument. -/
theorem isoProj_isComputableMap : IsComputableMap (DprimeUCodePresentation P) P (isoProj P) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (eIdx P t.unpair.2)) :=
    Nat.Primrec.pair Nat.Primrec.left ((eIdx_primrec P).comp Nat.Primrec.right)
  have hp : RecDecidable (fun t : ℕ => Yc P t.unpair.1 ⊆ Yc P (eIdx P t.unpair.2)) := by
    refine RecDecidable.of_iff (fun t => ?_) ((DprimeUCodePresentation P).incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl
  refine REPred.of_iff (fun t => ?_) hp.re
  show (isoProj P).rel ((DprimeUCodePresentation P).X t.unpair.1) (P.X t.unpair.2) ↔ _
  exact isoProj_rel_iff_incl P

end DomainTheory.NeighbourhoodSystems
