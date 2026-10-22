module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise415
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise416.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise416.optimalFix_le_sInf

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- **Exercise 4.16 (Scott 1981, PRG-19).** `optimalFix S` lies below every member of `S`. -/
theorem optimalFix_le (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) {s : V.Element} (hs : s ∈ S) :
    optimalFix f hf S hS hfix ≤ s :=
  le_trans (optimalFix_le_sInf f hf S hS hfix) (V.sInf_le S hS hs)

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
