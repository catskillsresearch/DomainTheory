/-ai
The neighbourhood system U is positive: the intersection of two neighbourhoods is a neighbourhood exactly when it is nonempty.

Present the two neighbourhoods by lists of intervals. A neighbourhood intersection is nonempty. Conversely, a nonempty intersection is presented by the combined interval list and is contained in the master because it is contained in the first neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem








/-- **`U` is Positive**: since `combineIntervals` presents *any* raw intersection of two presented
lists unconditionally, and `X ∩ Y ⊆ [0,1)` is automatic whenever `X ⊆ [0,1)`, only non-emptiness
can ever obstruct `U.mem (X ∩ Y)`. -/
theorem U_isPositive : U.IsPositive := by
  rintro X Y ⟨⟨L1, rfl⟩, -, hXsub⟩ ⟨⟨L2, rfl⟩, -, -⟩
  refine ⟨fun h => h.2.1, fun hne => ⟨⟨combineIntervals L1 L2, presentedIntervals_inter L1 L2⟩,
    hne, Set.inter_subset_left.trans hXsub⟩⟩

end DomainTheory.NeighbourhoodSystems
