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
