/-ai
If the source is a T₀ space and the sets U n form a topological basis, the embedding along U is injective and continuous.

The two conjuncts are the injectivity lemma and the continuity lemma for the embedding.
ai-/
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
public import DomainTheory.DataTypesAsLattices.Embedding.embed_injective
public import DomainTheory.DataTypesAsLattices.Embedding.embed_continuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function



theorem theorem_1_6_injective_continuous {X : Type*} [TopologicalSpace X]
    [T0Space X] (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    Injective (embed U) ∧ Continuous (embed U) :=
  ⟨embed_injective U hbasis, embed_continuous U hbasis⟩

end DomainTheory.DataTypesAsLattices
