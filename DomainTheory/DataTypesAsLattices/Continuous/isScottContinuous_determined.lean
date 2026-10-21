/-ai
Two Scott continuous maps that agree on every finite set are equal.

At an arbitrary element x, Scott continuity rewrites both values as Scott unions. The pieces of those unions agree because the maps agree on the finite set of each code.
ai-/
module

public import Mathlib.Topology.Bases
import all Mathlib.Topology.Bases
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
public import DomainTheory.DataTypesAsLattices.Continuous.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- Continuous functions are determined by their values on finite sets. -/
theorem isScottContinuous_determined {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g)
    (hfin : ∀ n, f (e n) = g (e n)) : f = g := by
  funext x
  rw [hf x, hg x]
  simp [scottUnion, scottPiece, hfin]

end DomainTheory.DataTypesAsLattices
