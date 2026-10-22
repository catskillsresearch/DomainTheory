module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Topology.Inseparable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.basicOpen
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.OpenFilter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.mem_basicOpen

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `[X ∩ Y] ⊆ [X]` whenever `X ∈ 𝒟`: a filter containing `X ∩ Y` contains `X` (upward closure).
This (with the symmetric version) is the closure of the basic opens under finite intersection,
i.e. `[X] ∩ [Y] = [X ∩ Y]`, the base condition behind the topology. -/
theorem basicOpen_inter_subset_left {X Y : Set α} (hX : V.mem X) :
    V.basicOpen (X ∩ Y) ⊆ V.basicOpen X :=
  fun z hz => z.up_mem hz hX Set.inter_subset_left

/-- `[X ∩ Y] ⊆ [Y]` whenever `Y ∈ 𝒟`. -/
theorem basicOpen_inter_subset_right {X Y : Set α} (hY : V.mem Y) :
    V.basicOpen (X ∩ Y) ⊆ V.basicOpen Y :=
  fun z hz => z.up_mem hz hY Set.inter_subset_right


/-- **Exercise 1.22 (the space).** The basic opens `[X]` (`X ∈ 𝒟`) generate a topology on `|𝒟|`:
`𝒰` is open iff it is a union of basic opens (condition (ii)). The three axioms hold because the
base is closed under finite intersection (`basicOpen_inter_subset_left/right`, using that filters
are `∩`-closed and upward closed) with `[Δ] = |𝒟|` covering the space. -/
instance instTopologicalSpaceElement : TopologicalSpace V.Element where
  IsOpen := V.OpenFilter
  isOpen_univ := ⟨fun x _ => ⟨V.master, x.master_mem, Set.subset_univ _⟩⟩
  isOpen_inter := by
    intro U W hU hW
    constructor
    intro x hx
    obtain ⟨hxU, hxW⟩ := hx
    obtain ⟨X, hX, hXU⟩ := hU.out x hxU
    obtain ⟨Y, hY, hYW⟩ := hW.out x hxW
    refine ⟨X ∩ Y, x.inter_mem hX hY, fun z hz => ⟨hXU ?_, hYW ?_⟩⟩
    · exact V.basicOpen_inter_subset_left (x.sub hX) hz
    · exact V.basicOpen_inter_subset_right (x.sub hY) hz
  isOpen_sUnion := by
    intro S hS
    constructor
    intro x hx
    obtain ⟨t, htS, hxt⟩ := hx
    obtain ⟨X, hX, hXt⟩ := (hS t htS).out x hxt
    exact ⟨X, hX, hXt.trans fun _ ha => ⟨t, htS, ha⟩⟩
end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
