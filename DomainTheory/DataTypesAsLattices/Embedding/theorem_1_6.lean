module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint
public import DomainTheory.DataTypesAsLattices.Embedding.Basic
public import DomainTheory.DataTypesAsLattices.Embedding.embed_inducing
public import DomainTheory.DataTypesAsLattices.Embedding.embed_injective

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function


/-- **Scott 1976, Theorem 1.6 (The embedding theorem).**
Every T₀ space with a countable basis embeds in `Pω`. -/
theorem theorem_1_6 {X : Type*} [TopologicalSpace X] [T0Space X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    IsEmbedding (embed U) where
  toIsInducing := embed_inducing U hbasis
  injective := embed_injective U hbasis

end DomainTheory.DataTypesAsLattices
