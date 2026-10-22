module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise328.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise328.val_le_leastMap_toElementMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise328.leastMapVals_bounded
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise328.leastMap_toElementMap_le_of_ub

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.le_sSup
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.sSup_le
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Exercise 3.28 (Scott 1981, PRG-19).** The least map's elementwise action is the least upper
bound of the active principal filters: `f₀(x) = ⊔ { ↑Yᵢ ∣ x ∈ [Xᵢ] }`. -/
theorem toElementMap_leastMap_eq_sSup (L : List (Set α × Set β))
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) (x : V₀.Element) :
    (leastMap L hL hcons).toElementMap x
      = V₁.sSup (leastMapVals L hL x) (leastMapVals_bounded hL hcons x) := by
  apply le_antisymm
  · apply leastMap_toElementMap_le_of_ub hL hcons
    intro w hw
    exact V₁.le_sSup _ (leastMapVals_bounded hL hcons x) hw
  · apply V₁.sSup_le
    rintro w ⟨p, hp, hp1x, rfl⟩
    exact val_le_leastMap_toElementMap hL hcons hp hp1x

end DomainTheory.NeighbourhoodSystems
