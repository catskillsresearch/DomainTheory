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
