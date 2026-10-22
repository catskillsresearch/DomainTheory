/-ai
The preimage of a Scott-open set under a map that preserves directed suprema is Scott-open.

Such a map is monotone, so the preimage is an upper set because the Scott-open set is. If the supremum of a nonempty directed set lies in the preimage, preservation puts the supremum of the image in the Scott-open set. The image is nonempty and directed by monotonicity, so some value of the map lies in the set, and the corresponding argument lies in the preimage.
ai-/
module

public import DomainTheory.ContinuousLattice.Specialization
public import Mathlib.Order.ScottContinuity
public import Mathlib.Topology.Order.ScottTopology
public import DomainTheory.ContinuousLattice.ScottMaps.Basic
public import DomainTheory.ContinuousLattice.ScottMaps.preservesDirectedSup_monotone

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']


theorem scottOpen_preimage {f : D → D'} (hf : PreservesDirectedSup f) {U : Set D'}
    (hU : ScottOpen U) : ScottOpen (f ⁻¹' U) := by
  have hmono := preservesDirectedSup_monotone hf
  refine ⟨fun a b hab ha => hU.1 (hmono hab) ha, fun S hS hSdir hmem => ?_⟩
  rw [Set.mem_preimage] at hmem
  have hmem' : sSup (f '' S) ∈ U := by rw [← hf hS hSdir]; exact hmem
  obtain ⟨s, hsS, hsU⟩ := hU.2 (Set.image_nonempty.2 hS)
    (fun s hs t ht => by
      obtain ⟨a, haS, rfl⟩ := hs
      obtain ⟨b, hbS, rfl⟩ := ht
      obtain ⟨c, hcS, hac, hbc⟩ := hSdir a haS b hbS
      exact ⟨f c, Set.mem_image_of_mem f hcS, hmono hac, hmono hbc⟩) hmem'
  obtain ⟨a, haS, rfl⟩ := hsS
  exact ⟨a, haS, Set.mem_preimage.2 hsU⟩

end DomainTheory.ContinuousLattice
