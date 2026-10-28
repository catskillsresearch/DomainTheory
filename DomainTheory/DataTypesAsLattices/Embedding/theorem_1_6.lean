module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Embedding.extend
public import DomainTheory.DataTypesAsLattices.Embedding.embed

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function

theorem theorem_1_6 {X : Type*} [TopologicalSpace X] [T0Space X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    IsEmbedding (embed U) where
  toIsInducing := embed.inducing U hbasis
  injective := embed.injective U hbasis

theorem theorem_1_6.injective_continuous {X : Type*} [TopologicalSpace X]
    [T0Space X] (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    Injective (embed U) ∧ Continuous (embed U) :=
  ⟨embed.injective U hbasis, embed.continuous U hbasis⟩

end DomainTheory.DataTypesAsLattices
