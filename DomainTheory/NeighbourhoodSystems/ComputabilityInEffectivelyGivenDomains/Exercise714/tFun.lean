module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise714

open NeighborhoodSystem Domain.Recursive DomainTheory.NeighbourhoodSystems

variable {β : Type*}

/-- The **running-intersection enumeration** of a computable element: `tFun Q r 0 = r 0` and
`tFun Q r (i+1) = Q.inter (tFun Q r i) (r (i+1))`. As `i` grows it lists the meet of the first `i+1`
members `Y_{r 0}, …, Y_{r i}` of the element, giving a *decreasing* chain of neighbourhoods. -/
def tFun {W : NeighborhoodSystem β} (Q : ComputablePresentation W) (r : ℕ → ℕ) (n : ℕ) :
    ℕ :=
  Nat.rec (motive := fun _ => ℕ) (r 0) (fun y IH => Q.inter IH (r (y + 1))) n

end DomainTheory.NeighbourhoodSystems.Exercise714
