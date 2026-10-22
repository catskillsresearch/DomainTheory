module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint
public import DomainTheory.DataTypesAsLattices.Embedding.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function


theorem embed_continuous {X : Type*} [TopologicalSpace X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    Continuous (embed U) :=
  continuous_generateFrom_iff.2 fun t ⟨n, hn⟩ => by
    subst hn
    change IsOpen (U n)
    exact hbasis.isOpen ⟨n, rfl⟩

end DomainTheory.DataTypesAsLattices
