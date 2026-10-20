module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}





section Smash






/-- **The compactness lemma.** If neither coordinate of `z` is `⊥`, some *proper* smash
neighbourhood witnesses `z.mem Y ⊆ Z` for any `Z ∈ z` — built from `exists_mem_ne_master_of_ne_bot`
witnesses on each coordinate, intersected against `Z`'s own decomposition via the *filter*
`inter_mem` of `z.fst`/`z.snd` (no `NeighborhoodSystem`-level consistency witness needed). -/
theorem exists_smash_witness {z : (prod D E).Element} (hx : z.fst ≠ D.bot) (hy : z.snd ≠ E.bot)
    {Z : Set (α ⊕ β)} (hzZ : z.mem Z) :
    ∃ Y, (Exercise510.smash D E).mem Y ∧ z.mem Y ∧ Y ⊆ Z := by
  obtain ⟨X0, hX0, hX0ne⟩ := exists_mem_ne_master_of_ne_bot hx
  obtain ⟨Y0, hY0, hY0ne⟩ := exists_mem_ne_master_of_ne_bot hy
  set A := Sum.inl ⁻¹' Z with hA
  set B := Sum.inr ⁻¹' Z with hB
  have hZeq : Z = prodNbhd A B := prodNbhd_preimage (z.sub hzZ)
  have hAmem : D.mem A := prod_mem_inl (z.sub hzZ)
  have hBmem : E.mem B := prod_mem_inr (z.sub hzZ)
  rw [hZeq] at hzZ
  have hzfA : z.fst.mem A := mem_fst.mpr ⟨hAmem, ((prod_mem_split hAmem hBmem).mp hzZ).1⟩
  have hzsB : z.snd.mem B := mem_snd.mpr ⟨hBmem, ((prod_mem_split hAmem hBmem).mp hzZ).2⟩
  have hzfX0' : z.fst.mem (X0 ∩ A) := z.fst.inter_mem hX0 hzfA
  have hzsY0' : z.snd.mem (Y0 ∩ B) := z.snd.inter_mem hY0 hzsB
  have hX0'mem : D.mem (X0 ∩ A) := z.fst.sub hzfX0'
  have hY0'mem : E.mem (Y0 ∩ B) := z.snd.sub hzsY0'
  have hX0'ne : X0 ∩ A ≠ D.master := Exercise510.inter_ne_master_left (z.fst.sub hX0) hX0ne
  have hY0'ne : Y0 ∩ B ≠ E.master := Exercise510.inter_ne_master_right (z.snd.sub hY0) hY0ne
  refine ⟨prodNbhd (X0 ∩ A) (Y0 ∩ B),
    Exercise510.smash_mem_proper hX0'mem hX0'ne hY0'mem hY0'ne, ?_, ?_⟩
  · exact (prod_mem_split hX0'mem hY0'mem).mpr
      ⟨(mem_fst.mp hzfX0').2, (mem_snd.mp hzsY0').2⟩
  · rw [hZeq]
    exact prodNbhd_subset_iff.mpr ⟨Set.inter_subset_right, Set.inter_subset_right⟩

end Smash
end DomainTheory.NeighbourhoodSystems
