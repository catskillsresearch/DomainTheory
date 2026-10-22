module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.Basic

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.le_sInf
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.27 — `⊔X` is an upper bound.** Each `x ∈ X` satisfies `x ⊑ ⊔X`. -/
theorem le_sSup (X : Set V.Element) (hX : V.Bounded X) {x : V.Element} (hx : x ∈ X) :
    x ≤ V.sSup X hX :=
  V.le_sInf (V.upperBounds X) (V.upperBounds_nonempty hX) x (fun _ hy => hy x hx)

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
