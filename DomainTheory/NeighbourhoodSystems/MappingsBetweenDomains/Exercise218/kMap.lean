module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_cons
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut_single
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut_cons
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut_mono

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- **Exercise 2.18 — the left inverse `k : 𝔹 → 𝔹`.** `X k Y ↔ ∃ σ, X = σΣ* ∧ Y ∈ 𝔹 ∧ (kOut σ)Σ* ⊆ Y`. -/
def kMap : ApproximableMap B B where
  rel X Y := ∃ σ, X = cone σ ∧ B.mem Y ∧ cone (kOut σ) ⊆ Y
  rel_dom := fun ⟨σ, hX, _, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hYmem, _⟩ => hYmem
  master_rel := by
    refine ⟨[], (B_master).trans cone_nil.symm, B.master_mem, ?_⟩
    rw [kOut_nil, B_master, cone_nil]
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hYmem, hYsub⟩ ⟨σ', hX', hY'mem, hY'sub⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    have hsub : cone (kOut σ) ⊆ Y ∩ Y' := Set.subset_inter hYsub hY'sub
    exact ⟨σ, hX, B.inter_mem hYmem hY'mem (memB_cone (kOut σ)) hsub, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, _, hYsub⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp; rw [← hX'cone, ← hX]; exact hX'X
    have hcone : cone (kOut σ') ⊆ cone (kOut σ) := cone_subset_cone.mpr (kOut_mono hpre)
    exact ⟨σ', hX'cone, hY'mem, (hcone.trans hYsub).trans hYY'⟩

end DomainTheory.NeighbourhoodSystems.Exercise218
