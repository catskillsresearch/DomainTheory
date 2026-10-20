/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_component

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- The `𝒟^∞`-element determined by an infinite sequence `⟨xₙ⟩` of `𝒟`-elements: the neighbourhoods
`W` whose every fiber lies in the corresponding `xᵢ`. -/
def ofSeq (seq : ℕ → V.Element) : (iterSys V).Element where
  mem W := (iterSys V).mem W ∧ ∀ i, (seq i).mem (fiber W i)
  sub h := h.1
  master_mem := ⟨(iterSys V).master_mem, fun i => by
    rw [fiber_iterSys_master]; exact (seq i).master_mem⟩
  inter_mem := by
    rintro W W' ⟨hW, hWf⟩ ⟨hW', hW'f⟩
    refine ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩
    · rw [fiber_inter]; exact (seq i).sub ((seq i).inter_mem (hWf i) (hW'f i))
    · obtain ⟨NW, hNW⟩ := hW.2
      obtain ⟨NW', hNW'⟩ := hW'.2
      refine ⟨max NW NW', fun i hi => ?_⟩
      rw [fiber_inter, hNW i (le_trans (le_max_left _ _) hi),
        hNW' i (le_trans (le_max_right _ _) hi), Set.inter_self]
    · rw [fiber_inter]; exact (seq i).inter_mem (hWf i) (hW'f i)
  up_mem := by
    rintro W W' ⟨_, hWf⟩ hW' hWW'
    exact ⟨hW', fun i => (seq i).up_mem (hWf i) (hW'.1 i) (fiber_mono hWW' i)⟩

end DomainTheory.NeighbourhoodSystems
