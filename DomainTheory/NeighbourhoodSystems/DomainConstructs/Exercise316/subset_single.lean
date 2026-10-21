/-ai
Every neighbourhood of the infinite iterate is contained in the pinning of any chosen copy to that neighbourhood's own fiber at the chosen copy.

Unfold the pinning on a pair in the neighbourhood. If the index is the chosen copy, the pair is membership in the fiber. Otherwise the token lies in a fiber of a neighbourhood, hence in the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_iterSys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- Every `𝒟^∞`-neighbourhood is contained in the pinning of its own `i`-th fiber. -/
theorem subset_single {W : Set (ℕ × α)} (hW : (iterSys V).mem W) (i : ℕ) :
    W ⊆ single V i (fiber W i) := by
  rintro ⟨j, a⟩ ha
  simp only [single, Set.mem_ofPred_eq]
  by_cases h : j = i
  · rw [ite_eq_left h]; subst h; exact ha
  · rw [ite_eq_right h]; exact V.sub_master (hW.1 j) ha

end DomainTheory.NeighbourhoodSystems
