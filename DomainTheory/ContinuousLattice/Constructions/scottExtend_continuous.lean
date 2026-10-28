module
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice

public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.Constructions.scottExtend
public import DomainTheory.ContinuousLattice.Constructions.scottExtend_aux_directed
public import DomainTheory.ContinuousLattice.Constructions.scottExtend_aux_nonempty
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import Mathlib.Topology.Defs.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]

section InjectiveExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]

omit [TopologicalSpace X] in

theorem scottExtend_continuous (hE : ContinuousLattice E) (e : X → Y) (f : X → E) :
    @Continuous Y E _ scottTopologicalSpace (scottExtend e f) := by
  let : TopologicalSpace E := scottTopologicalSpace
  rw [continuous_def]
  intro U hU
  rw [ScottOpen.isOpen_iff] at hU
  rw [isOpen_iff_forall_mem_open]
  intro y₀ hy₀
  have hgy₀U : scottExtend e f y₀ ∈ U := hy₀
  obtain ⟨a, haz, hasub⟩ := exists_wayBelow_subset hE hU hgy₀U
  obtain ⟨d, hd, had⟩ := (WayBelow.sSup_iff (scottExtend_aux_nonempty e f y₀)
    (scottExtend_aux_directed e f y₀)).1 haz
  obtain ⟨V, hVo, hy₀V, rfl⟩ := hd
  refine ⟨V, ?_, hVo, hy₀V⟩
  intro y' hy'V
  show scottExtend e f y' ∈ U
  refine hasub ?_
  show a ≪ scottExtend e f y'
  exact had.trans_le (le_sSup ⟨V, hVo, hy'V, rfl⟩)

end InjectiveExtension
end DomainTheory.ContinuousLattice
