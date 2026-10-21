/-ai
This file states Exercise 4.16. For a nonempty set of fixed points of a monotone endomap of a domain, the image of the infimum lies below the infimum, because it lies below the image of each member and each member equals its image. The monotone construction of Exercise 4.13 therefore yields a least fixed point below the infimum and below every member. Each member is an upper bound of that fixed point, so the fixed point is consistent with every member of the set. The file imports the constructions of Exercises 4.13 and 4.15, the optimal fixed point, and the infimum inequality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise415
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise416.optimalFix
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise416.f_sInf_le

@[expose] public section

/-!
# Exercise 4.16 (Scott 1981, PRG-19, Lecture IV) — the *optimal* fixed point

(For fixed-point nuts.) Scott's step (1): for any *non-empty* set `S` of fixed points of a monotone
`f : |𝒟| → |𝒟|`, the greatest lower bound `⋂S` (Exercise 1.18 `sInf`) satisfies

  `f(⋂S) ⊑ ⋂S`               (`f_sInf_le`)

— indeed `f(⋂S) ⊑ f(s) = s` for each `s ∈ S`, so `f(⋂S)` is a lower bound of `S`. Being a pre-fixed
point, `⋂S` carries (Exercise 4.13(1)'s `monoFix`) the least fixed point `optimalFix S` with

  `optimalFix S ⊑ ⋂S ⊑ s`   for every `s ∈ S`   (`optimalFix_le`),

so `optimalFix S` is a fixed point lying **below** every member of `S`, and it is **consistent** with
each `s ∈ S` (their common upper bound is `s` itself, `optimalFix_consistent`). Taking `S` to be the
set of *maximal* fixed points (which exist by Exercise 4.15) gives the fixed point that is below all
the maximal ones, consistent with all other fixed points — Scott's "optimal" fixed point.

The data (`optimalFix`) is **choice-free**; only the *appeal to* Exercise 4.15 for the supply of
maximal fixed points is classical.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
