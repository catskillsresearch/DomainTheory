/-ai
If the sets U n form a topological basis, the embedding along U is continuous as a map into Pω.

Continuity into the generated topology reduces to openness of the preimage of each subbasic open. That preimage is the corresponding basis element U n, which is open because it belongs to the basis.
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
