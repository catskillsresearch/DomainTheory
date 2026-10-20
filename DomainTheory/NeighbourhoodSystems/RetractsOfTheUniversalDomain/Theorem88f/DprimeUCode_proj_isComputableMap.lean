module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.isomorphic_DprimeUCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.DprimeUCode_isEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **The projection `j : U → D''` is computable.** `j`'s relation `UX m \, j \, Yc P n` reduces to
the raw code-level subset test `UX m ⊆ UX (YseqCode P n)`, decidable by reindexing
`UComputablePresentation.incl_computable` along `YseqCode P` in the second argument. -/
theorem DprimeUCode_proj_isComputableMap :
    IsComputableMap UComputablePresentation (DprimeUCodePresentation P)
      (DprimeUCode_subsystem P).proj := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (YseqCode P t.unpair.2)) :=
    Nat.Primrec.pair Nat.Primrec.left ((primrec_YseqCode P).comp Nat.Primrec.right)
  have hp : RecDecidable (fun t : ℕ => UX t.unpair.1 ⊆ UX (YseqCode P t.unpair.2)) := by
    refine RecDecidable.of_iff (fun t => ?_) (UComputablePresentation.incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl
  refine REPred.of_iff (fun t => ?_) hp.re
  show (DprimeUCode_subsystem P).proj.rel (UX t.unpair.1) (Yc P t.unpair.2) ↔ _
  rw [Subsystem.proj_rel]
  exact ⟨fun ⟨_, _, hsub⟩ => hsub,
    fun hsub => ⟨U_mem_UX _, ⟨t.unpair.2, rfl⟩, hsub⟩⟩

end DomainTheory.NeighbourhoodSystems
