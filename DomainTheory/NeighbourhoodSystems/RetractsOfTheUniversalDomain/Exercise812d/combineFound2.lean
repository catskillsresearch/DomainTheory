module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- **Combine two `(found, code)` packed fold results into one**: union their codes via `hUnion`
when both found something, and simply propagate whichever single side found something otherwise
(mirroring `XFoldStep`/`YFoldStep`'s own "skip junk, else union" shape one level up). Generic in any
`IsComputableUnion`, reused below for `YPseqCode`'s "outer 2-way union" of its two `bx`-fixed inner
folds. -/
noncomputable def combineFound2 {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hUnion : IsComputableUnion Q) (r0 r1 : ℕ) : ℕ :=
  selectFn r0.unpair.1
    (selectFn r1.unpair.1 (Nat.pair 1 (hUnion.unionIdx r0.unpair.2 r1.unpair.2)) r0)
    r1

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace combineFound2

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem found_iff {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hUnion : IsComputableUnion Q) {r0 r1 : ℕ}
    (h0 : r0.unpair.1 ≤ 1) (h1 : r1.unpair.1 ≤ 1) :
    (combineFound2 hUnion r0 r1).unpair.1 = 1 ↔ r0.unpair.1 = 1 ∨ r1.unpair.1 = 1 := by
  unfold combineFound2
  rcases Nat.eq_zero_or_pos r0.unpair.1 with hr0 | hr0
  · rw [hr0, selectFn_zero]; omega
  · rw [show r0.unpair.1 = 1 from by omega, selectFn_one]
    rcases Nat.eq_zero_or_pos r1.unpair.1 with hr1 | hr1
    · rw [hr1, selectFn_zero]; omega
    · rw [show r1.unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]; omega

end combineFound2
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace combineFound2

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem mem_iff {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hpos : W.IsPositive) (hdiff : W.DiffClosed)
    (hnomin : W.NoMinimal) (hUnion : IsComputableUnion Q) {r0 r1 : ℕ}
    (h0 : r0.unpair.1 ≤ 1) (h1 : r1.unpair.1 ≤ 1)
    (hmem0 : r0.unpair.1 = 1 → W.mem (Q.X r0.unpair.2))
    (hmem1 : r1.unpair.1 = 1 → W.mem (Q.X r1.unpair.2))
    (hfound : (combineFound2 hUnion r0 r1).unpair.1 = 1) (z : γ) :
    z ∈ Q.X (combineFound2 hUnion r0 r1).unpair.2 ↔
      (r0.unpair.1 = 1 ∧ z ∈ Q.X r0.unpair.2) ∨ (r1.unpair.1 = 1 ∧ z ∈ Q.X r1.unpair.2) := by
  unfold combineFound2 at hfound ⊢
  rcases Nat.eq_zero_or_pos r0.unpair.1 with hr0 | hr0
  · rw [hr0, selectFn_zero] at hfound ⊢
    constructor
    · intro hz; exact Or.inr ⟨hfound, hz⟩
    · rintro (⟨h, -⟩ | ⟨-, hz⟩)
      · omega
      · exact hz
  · rw [show r0.unpair.1 = 1 from by omega, selectFn_one] at hfound ⊢
    have hmem0' := hmem0 (by omega)
    rcases Nat.eq_zero_or_pos r1.unpair.1 with hr1 | hr1
    · rw [hr1, selectFn_zero] at hfound ⊢
      constructor
      · intro hz; exact Or.inl ⟨by omega, hz⟩
      · rintro (⟨-, hz⟩ | ⟨h, -⟩)
        · exact hz
        · omega
    · rw [show r1.unpair.1 = 1 from by omega, selectFn_one, unpair_pair_snd]
      have hmem1' := hmem1 (by omega)
      have hex : ∃ k, Q.X k = Q.X r0.unpair.2 ∪ Q.X r1.unpair.2 :=
        Q.surj (NeighborhoodSystem.mem_union_of_mem hpos hdiff hnomin hmem0' hmem1')
      rw [hUnion.unionIdx_spec hex, Set.mem_union]
      constructor
      · rintro (hz | hz)
        · exact Or.inl ⟨by omega, hz⟩
        · exact Or.inr ⟨by omega, hz⟩
      · rintro (⟨-, hz⟩ | ⟨-, hz⟩)
        · exact Or.inl hz
        · exact Or.inr hz

end combineFound2
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace combineFound2

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem mem_of_found {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hpos : W.IsPositive) (hdiff : W.DiffClosed)
    (hnomin : W.NoMinimal) (hUnion : IsComputableUnion Q) {r0 r1 : ℕ}
    (h0 : r0.unpair.1 ≤ 1) (h1 : r1.unpair.1 ≤ 1)
    (hmem0 : r0.unpair.1 = 1 → W.mem (Q.X r0.unpair.2))
    (hmem1 : r1.unpair.1 = 1 → W.mem (Q.X r1.unpair.2)) :
    (combineFound2 hUnion r0 r1).unpair.1 = 1 →
      W.mem (Q.X (combineFound2 hUnion r0 r1).unpair.2) := by
  unfold combineFound2
  rcases Nat.eq_zero_or_pos r0.unpair.1 with hr0 | hr0
  · rw [hr0, selectFn_zero]
    exact hmem1
  · rw [show r0.unpair.1 = 1 from by omega, selectFn_one]
    have hmem0' := hmem0 (by omega)
    rcases Nat.eq_zero_or_pos r1.unpair.1 with hr1 | hr1
    · rw [hr1, selectFn_zero]
      exact fun _ => hmem0'
    · rw [show r1.unpair.1 = 1 from by omega, selectFn_one, unpair_pair_snd]
      intro _
      have hmem1' := hmem1 (by omega)
      have hex : ∃ k, Q.X k = Q.X r0.unpair.2 ∪ Q.X r1.unpair.2 :=
        Q.surj (NeighborhoodSystem.mem_union_of_mem hpos hdiff hnomin hmem0' hmem1')
      rw [hUnion.unionIdx_spec hex]
      exact NeighborhoodSystem.mem_union_of_mem hpos hdiff hnomin hmem0' hmem1'

end combineFound2
end DomainTheory.NeighbourhoodSystems
