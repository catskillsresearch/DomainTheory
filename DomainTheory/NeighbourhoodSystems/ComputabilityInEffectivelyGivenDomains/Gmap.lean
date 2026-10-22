module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_mono
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexG_subset_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexG_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_rel

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

/-- **The inverse map `G : (D^∞)^∞ → D^∞`** (reindexing fibers along `Nat.unpair`):
`S G W ↔ ∀ k, fiber2 S (unpair k).1 (unpair k).2 ⊆ fiber W k`. -/
def Gmap (V : NeighborhoodSystem α) : ApproximableMap (iterSys (iterSys V)) (iterSys V) where
  rel S W := (iterSys (iterSys V)).mem S ∧ (iterSys V).mem W ∧
    ∀ k, fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 ⊆ fiber W k
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(iterSys (iterSys V)).master_mem, (iterSys V).master_mem, fun k => by
    rw [fiber2_master, fiber_iterSys_master]⟩
  inter_right := by
    rintro S W W' ⟨hS, hW, hg⟩ ⟨-, hW', hg'⟩
    refine ⟨hS, (iterSys V).inter_mem hW hW' (reindexG_mem hS) ?_, fun k => ?_⟩
    · exact Set.subset_inter (reindexG_subset_iff.mpr hg) (reindexG_subset_iff.mpr hg')
    · rw [fiber_inter]; exact Set.subset_inter (hg k) (hg' k)
  mono := by
    rintro S S' W W' ⟨hS, hW, hg⟩ hS'S hWW' hS' hW'
    exact ⟨hS', hW', fun k => ((fiber2_mono hS'S _ _).trans (hg k)).trans (fiber_mono hWW' k)⟩

end Exercise718

end DomainTheory.NeighbourhoodSystems
