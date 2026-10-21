/-ai
Whenever some transferred neighbourhood sits inside the intersection of two transferred neighbourhoods, the transferred neighbourhood at the intersection index of the re-pointed presentation equals that intersection.

The witness transfers, by the embedding rule twice, to a witness for the enumerated neighbourhoods. The intersection specification of the re-pointed presentation therefore equates the enumerated neighbourhood at the intersection index with the intersection of the two enumerated neighbourhoods. The corresponding index sets are equal, and the intersection-transfer lemma, using containment in the universe, pushes the equation to the transferred neighbourhoods.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **The intersection index transfers.** `(P0 P).inter n m` — Scott's own primitive-recursive
intersection index for `D` (reused verbatim, no new index function) — also indexes `Yidx (e P) n ∩
Yidx (e P) m` whenever that intersection is consistent. -/
theorem DprimeU_inter_spec {n m : ℕ}
    (h : ∃ k, Yidx (e P) k ⊆ Yidx (e P) n ∩ Yidx (e P) m) :
    Yidx (e P) ((P0 P).inter n m) = Yidx (e P) n ∩ Yidx (e P) m := by
  have h' : ∃ k, (P0 P).X k ⊆ (P0 P).X n ∩ (P0 P).X m := by
    obtain ⟨k, hk⟩ := h
    rw [Set.subset_inter_iff] at hk
    exact ⟨k, Set.subset_inter ((embed_subset_iff (e P) k n).mpr hk.1)
      ((embed_subset_iff (e P) k m).mpr hk.2)⟩
  have heP : (P0 P).X ((P0 P).inter n m) = (P0 P).X n ∩ (P0 P).X m := (P0 P).inter_spec h'
  have hidx : idxSet (e P) n ∩ idxSet (e P) m = idxSet (e P) ((P0 P).inter n m) :=
    idxSet_inter_of_inter_eq (e P) heP.symm
  exact ((transfer_inter_eq_iff splitChoice (idxSet (e P)) Set.univ univ_nonempty_nat
    splitChoice_isSplitSpec n m ((P0 P).inter n m)
    (Set.subset_univ _) (Set.subset_univ _) (Set.subset_univ _)).mp hidx).symm

end DomainTheory.NeighbourhoodSystems
