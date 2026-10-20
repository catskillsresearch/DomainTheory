module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_inj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_proj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_projectionPair_isComputable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88n.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88n.isoInj_rel_iff_incl

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






/-- **`isoInj` is computable** relative to `P`/`DprimeUCodePresentation P`: its raw-index relation is
`incl_computable` reindexed by the primitive-recursive `eIdx P` in the second argument. -/
theorem isoInj_isComputableMap : IsComputableMap P (DprimeUCodePresentation P) (isoInj P) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (eIdx P t.unpair.2)) :=
    Nat.Primrec.pair Nat.Primrec.left ((eIdx_primrec P).comp Nat.Primrec.right)
  have hp : RecDecidable (fun t : ℕ => P.X t.unpair.1 ⊆ P.X (eIdx P t.unpair.2)) := by
    refine RecDecidable.of_iff (fun t => ?_) (P.incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine REPred.of_iff (fun t => ?_) hp.re
  show (isoInj P).rel (P.X t.unpair.1) ((DprimeUCodePresentation P).X t.unpair.2) ↔ _
  exact isoInj_rel_iff_incl P

end DomainTheory.NeighbourhoodSystems
