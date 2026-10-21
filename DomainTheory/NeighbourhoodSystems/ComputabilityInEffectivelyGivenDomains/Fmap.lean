/-ai
The forward map of the isomorphism between the iterated neighbourhood system and its iteration reindexes fibers along pairing. A neighbourhood of the iterated system is related to a neighbourhood of the twice iterated system when, for every pair of indices, the fiber at the paired index is contained in the double fiber at those indices. The master neighbourhood is related to the master neighbourhood because every fiber of the master is the master. The relation is closed under intersection on the right by closure of the iterated system under intersection and because the double fiber of an intersection is the intersection of the double fibers. It is monotone because fibers and double fibers are monotone.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_mono
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_inter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexF_subset_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexF_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

/-- **The forward map `F : D^∞ → (D^∞)^∞`** of `D^∞ ≅ (D^∞)^∞` (reindexing fibers along `Nat.pair`):
`W F S ↔ ∀ i j, fiber W (pair i j) ⊆ fiber2 S i j`. -/
def Fmap (V : NeighborhoodSystem α) : ApproximableMap (iterSys V) (iterSys (iterSys V)) where
  rel W S := (iterSys V).mem W ∧ (iterSys (iterSys V)).mem S ∧
    ∀ i j, fiber W (Nat.pair i j) ⊆ fiber2 S i j
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(iterSys V).master_mem, (iterSys (iterSys V)).master_mem, fun i j => by
    rw [fiber_iterSys_master, fiber2_master]⟩
  inter_right := by
    rintro W S S' ⟨hW, hS, hf⟩ ⟨-, hS', hf'⟩
    refine ⟨hW, (iterSys (iterSys V)).inter_mem hS hS' (reindexF_mem hW) ?_, fun i j => ?_⟩
    · exact Set.subset_inter (reindexF_subset_iff.mpr hf) (reindexF_subset_iff.mpr hf')
    · rw [fiber2_inter]; exact Set.subset_inter (hf i j) (hf' i j)
  mono := by
    rintro W W' S S' ⟨hW, hS, hf⟩ hW'W hSS' hW' hS'
    exact ⟨hW', hS', fun i j => ((fiber_mono hW'W _).trans (hf i j)).trans (fiber2_mono hSS' i j)⟩

end Exercise718

end DomainTheory.NeighbourhoodSystems
