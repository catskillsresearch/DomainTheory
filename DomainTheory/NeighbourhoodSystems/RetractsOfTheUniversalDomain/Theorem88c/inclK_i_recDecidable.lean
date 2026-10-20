module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **`Yidx (e P) i ⊆ Yidx (e P) j`, reindexed.** A thin wrapper packaging two `incl_computable`-style
facts (`(P0 P).X k ⊆ (P0 P).X i`, resp. `j`) as `RecDecidable₃`, ready to combine with the `DAtom`
decider above. -/
theorem inclK_i_recDecidable :
    RecDecidable₃ (fun i _ k => (P0 P).X k ⊆ (P0 P).X i) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.2.unpair.2 t.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right) Nat.Primrec.left
  have hp := (P0 P).incl_computable.comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems
