/-ai
For a nonempty set of fixed points of a monotone endomap, the image of the infimum lies below the infimum.

It is enough to lie below each member of the set. Monotonicity places the image of the infimum below the image of the member, and the fixed-point equation replaces that image by the member.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise415

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-- **Exercise 4.16(1) (Scott 1981, PRG-19).** Scott's formula: for a non-empty set `S` of fixed
points, `f(⋂S) ⊑ ⋂S`. (`f(⋂S) ⊑ f(s) = s` for each `s ∈ S`, then take the glb.) -/
theorem f_sInf_le (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) : f (V.sInf S hS) ≤ V.sInf S hS := by
  apply V.le_sInf
  intro s hsS
  calc f (V.sInf S hS) ≤ f s := hf (V.sInf_le S hS hsS)
    _ = s := hfix s hsS

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
