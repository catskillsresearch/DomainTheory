
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Set.Finite.Powerset

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

/-- Scott's auxiliary value `0'` used in the many-valued tables of Theorem 6.7.
    The vision transcription writes `0' = 0 ∪ ⊥`, which equals `0` and would
    collapse the tables; the tables need a point distinct from `⊥`, `0`, and
    `⊤`, so we take `0 ∪ 1`. -/
def zeroPrime : Pomega := ofNat 0 ∪ ofNat 1

end DomainTheory.DataTypesAsLattices
