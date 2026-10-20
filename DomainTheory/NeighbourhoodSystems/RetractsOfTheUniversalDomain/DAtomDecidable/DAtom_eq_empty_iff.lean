module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.isomorphic_DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.mem_DAtom
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.meetFold_spec

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable (cons : ℕ → ℕ)





/-- **The core emptiness characterization.** `DAtom pos neg` is empty iff either the positive
part is inconsistent, or the meet's own index `idx` already lies inside some negative target
`Xⱼ` (forcing every candidate below it there too). -/
theorem DAtom_eq_empty_iff
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (pos neg : List ℕ) :
    DAtom P pos neg = ∅ ↔
      (meetFold P cons pos).unpair.1 ≠ 1 ∨
        ∃ j ∈ neg, P.X (meetFold P cons pos).unpair.2 ⊆ P.X j := by
  obtain ⟨hle, h1, h0⟩ := meetFold_spec P cons hcons pos
  set r := meetFold P cons pos with hrdef
  rcases (show r.unpair.1 = 0 ∨ r.unpair.1 = 1 by omega) with hr | hr
  · have hIPos : IPos P pos = ∅ := h0 hr
    simp only [hr, ne_eq, zero_ne_one, not_false_eq_true, true_or, iff_true]
    ext m
    simp only [DAtom, hIPos, Set.mem_inter_iff, Set.mem_empty_iff_false, false_and,
      Set.mem_empty_iff_false]
  · have hIPos : idxSet P.X r.unpair.2 = IPos P pos := h1 hr
    simp only [hr, ne_eq, not_true_eq_false, false_or]
    constructor
    · intro hempty
      by_contra hcon
      push Not at hcon
      have hmem : r.unpair.2 ∈ DAtom P pos neg := by
        rw [mem_DAtom]
        refine ⟨fun i hi => ?_, fun j hj => ?_⟩
        · have hself : r.unpair.2 ∈ IPos P pos := hIPos ▸ self_mem_idxSet P.X r.unpair.2
          exact hself i hi
        · exact hcon j hj
      rw [hempty] at hmem
      exact absurd hmem (Set.notMem_empty _)
    · rintro ⟨j, hj, hsub⟩
      ext m
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro hmem
      rw [mem_DAtom] at hmem
      have hmsub : P.X m ⊆ P.X r.unpair.2 := by
        have hmI : m ∈ IPos P pos := hmem.1
        rw [← hIPos] at hmI
        exact hmI
      exact hmem.2 j hj (hmsub.trans hsub)

end DomainTheory.NeighbourhoodSystems
