module

public import Mathlib.Topology.Bases
import all Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
import all Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
import all Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint
public import DomainTheory.DataTypesAsLattices.Embedding.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function



theorem embed_inducing {X : Type*} [TopologicalSpace X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    IsInducing (embed U) := by
  refine ⟨?_⟩
  rw [hbasis.eq_generateFrom]
  change generateFrom (Set.range U) =
    (generateFrom (Set.range memOpen)).induced (embed U)
  rw [induced_generateFrom_eq]
  congr 1
  ext V
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨memOpen n, ⟨n, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩

end DomainTheory.DataTypesAsLattices
