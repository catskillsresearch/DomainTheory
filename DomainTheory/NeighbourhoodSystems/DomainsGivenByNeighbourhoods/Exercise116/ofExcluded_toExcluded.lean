/-ai
The filter of the excluded-point set of a cofinite filter equals the original filter.

By extensionality, a neighbourhood lies in the reconstructed filter when its complement is finite and contained in the excluded-point set. The reconstruction lemma then places the complement of that complement in the original filter. Conversely, if the neighbourhood lies in the original filter, its complement is finite, and each point of the complement has its singleton complement in the filter by upward closure along the inclusion of the neighbourhood in that singleton complement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.ofExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_ofExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.toExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_toExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_compl_singleton
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_compl_of_finite
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.subset_compl_singleton

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

theorem ofExcluded_toExcluded (x : cofiniteSystem.Element) :
    ofExcluded (toExcluded x) = x := by
  apply Element.ext
  intro Y
  rw [mem_ofExcluded]
  constructor
  · rintro ⟨hfin, hsub⟩
    have h := mem_compl_of_finite x hfin (fun n hn => mem_toExcluded.mp (hsub hn))
    rwa [compl_compl] at h
  · intro hxY
    refine ⟨x.sub hxY, ?_⟩
    intro n hn
    rw [mem_toExcluded]
    exact x.up_mem hxY (mem_compl_singleton n) (subset_compl_singleton hn)

end Cofinite

end DomainTheory.NeighbourhoodSystems
