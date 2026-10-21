/-ai
The injection from the code-driven subsystem D'' into the universal system is a computable map of the two presentations.

Pairing the Y-sequence code of the first component with the second component is primitive recursive, and the universal presentation's inclusion decider composed with it decides inclusion of the corresponding U-neighbourhoods. That decidable predicate is recursively enumerable. The injection relation unfolds to this inclusion together with the two membership facts, which hold because a coded set is the neighbourhood of its index and the U-neighbourhood of a code belongs to the universal system.
ai-/
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

/-- **The injection `i : D'' → U` is computable.** `i`'s relation `Yc P n \, i \, UX m` reduces to
the raw code-level subset test `UX (YseqCode P n) ⊆ UX m`, decidable by reindexing
`UComputablePresentation.incl_computable` along `YseqCode P` in the first argument. -/
theorem DprimeUCode_inj_isComputableMap :
    IsComputableMap (DprimeUCodePresentation P) UComputablePresentation
      (DprimeUCode_subsystem P).inj := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (YseqCode P t.unpair.1) t.unpair.2) :=
    Nat.Primrec.pair ((primrec_YseqCode P).comp Nat.Primrec.left) Nat.Primrec.right
  have hp : RecDecidable (fun t : ℕ => UX (YseqCode P t.unpair.1) ⊆ UX t.unpair.2) := by
    refine RecDecidable.of_iff (fun t => ?_) (UComputablePresentation.incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl
  refine REPred.of_iff (fun t => ?_) hp.re
  show (DprimeUCode_subsystem P).inj.rel (Yc P t.unpair.1) (UX t.unpair.2) ↔ _
  rw [Subsystem.inj_rel]
  exact ⟨fun ⟨_, _, hsub⟩ => hsub,
    fun hsub => ⟨⟨t.unpair.1, rfl⟩, U_mem_UX _, hsub⟩⟩

end DomainTheory.NeighbourhoodSystems
