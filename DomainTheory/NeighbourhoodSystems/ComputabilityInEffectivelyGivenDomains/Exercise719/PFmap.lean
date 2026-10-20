module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PDmem_down

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}

/-- **Exercise 7.19 (Scott 1981, PRG-19) — the functorial action `ℙf : ℙD → ℙE`.** Given an
approximable map `f : D → E`, the relation between `ℙD`- and `ℙE`-neighbourhoods is "every member of
the source is `f`-related to some member of the target". This is the representation-independent form
of Scott's displayed `∀ i < n ∃ j < m. Xᵢ f Yⱼ` (see `PFmap_rel_fin`). -/
def PFmap (f : ApproximableMap V W) : ApproximableMap V.PowerDomain W.PowerDomain where
  rel A B := V.PDmem A ∧ W.PDmem B ∧ ∀ X ∈ A, ∃ Y ∈ B, f.rel X Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨V.PDmem_master, W.PDmem_master, ?_⟩
    rintro X ⟨hXmem, hXsub⟩
    exact ⟨W.master, ⟨W.master_mem, subset_rfl⟩,
      f.mono f.master_rel hXsub subset_rfl hXmem W.master_mem⟩
  inter_right := by
    rintro A B B' ⟨hA, hB, hbody⟩ ⟨-, hB', hbody'⟩
    refine ⟨hA, W.PDmem_inter hB hB', ?_⟩
    intro X hX
    obtain ⟨Y, hYB, hrel⟩ := hbody X hX
    obtain ⟨Y', hY'B', hrel'⟩ := hbody' X hX
    have hinmem : W.mem (Y ∩ Y') := f.rel_cod (f.inter_right hrel hrel')
    exact ⟨Y ∩ Y', Set.mem_inter
      (W.PDmem_down hB hYB Set.inter_subset_left hinmem)
      (W.PDmem_down hB' hY'B' Set.inter_subset_right hinmem),
      f.inter_right hrel hrel'⟩
  mono := by
    rintro A A' B B' ⟨_, _, hbody⟩ hA'A hBB' hA' hB'
    refine ⟨hA', hB', ?_⟩
    intro X hX
    obtain ⟨Y, hYB, hrel⟩ := hbody X (hA'A hX)
    exact ⟨Y, hBB' hYB, hrel⟩

end DomainTheory.NeighbourhoodSystems
