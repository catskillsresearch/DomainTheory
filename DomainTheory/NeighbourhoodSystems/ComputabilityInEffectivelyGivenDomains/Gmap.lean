/-ai
The inverse map of the isomorphism between the iterated neighbourhood system and its iteration reindexes fibers along unpairing. A neighbourhood of the twice iterated system is related to a neighbourhood of the iterated system when, for every index, the double fiber at the two components of its unpairing is contained in the fiber at that index. The master neighbourhood is related to the master neighbourhood because every fiber of the master is the master. The relation is closed under intersection on the right by closure under intersection and because the fiber of an intersection is the intersection of the fibers. It is monotone because double fibers and fibers are monotone.
ai-/
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
