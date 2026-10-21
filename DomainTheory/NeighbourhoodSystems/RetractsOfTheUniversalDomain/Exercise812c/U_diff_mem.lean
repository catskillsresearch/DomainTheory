/-ai
The difference of two neighbourhoods of U is empty or a neighbourhood of U.

Present the two neighbourhoods by lists of intervals. The difference of the presented intervals is empty, or else nonempty and presented by the difference of the lists, and it remains inside the master because it is contained in the first neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


/-- **`U` is closed under set-difference of two of its own neighbourhoods** (or the difference is
empty): `IntervalPrimrec.lean`'s `diffLists`/`presentedIntervals_diffLists`, built unconditionally
from `Ico_diff_Ico`, already witnesses presentability of the raw difference; only non-emptiness can
fail. -/
theorem U_diff_mem {X Y : Set ℚ} (hX : U.mem X) (hY : U.mem Y) : X \ Y = ∅ ∨ U.mem (X \ Y) := by
  obtain ⟨⟨L1, rfl⟩, -, hXsub⟩ := hX
  obtain ⟨⟨L2, rfl⟩, -, -⟩ := hY
  rcases Set.eq_empty_or_nonempty (presentedIntervals L1 \ presentedIntervals L2) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨⟨diffLists L1 L2, (presentedIntervals_diffLists L1 L2).symm⟩, h,
      Set.sdiff_subset.trans hXsub⟩

end DomainTheory.NeighbourhoodSystems
