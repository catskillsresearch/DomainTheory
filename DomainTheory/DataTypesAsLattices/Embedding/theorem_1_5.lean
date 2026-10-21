/-ai
Scott 1976, Theorem 1.5, the extension theorem, in its continuity clause: the extension of a map from a subspace into Pω is continuous on the ambient space.

Continuity into the generated topology reduces to the preimage of each subbasic open. The preimage of the subbasic open of k is open by the openness lemma for membership in the extension.
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
public import DomainTheory.DataTypesAsLattices.Embedding.isOpen_extend_mem

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function


/-- **Scott 1976, Theorem 1.5 (The extension theorem), continuity.** -/
theorem theorem_1_5 {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) : Continuous (extend (Y := Y) (X := X) f) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨k, rfl⟩
  exact isOpen_extend_mem f k

end DomainTheory.DataTypesAsLattices
