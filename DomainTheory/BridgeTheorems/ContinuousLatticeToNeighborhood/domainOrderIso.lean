/-ai
Assuming a complete lattice D is continuous, domainOrderIso is the order isomorphism between D and the round filters of the way-below neighbourhood system. It sends an element to its principal filter, which is round, and sends a round filter to the retraction of its underlying filter. The two composites are the identity. The forward map reflects order by comparing retractions of principal filters, using that a code of the source principal filter is way-below the source and remains a code of the target, and it preserves order by monotonicity of the principal filter.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter_mono
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.mem_wayBelowUp_toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.ofFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter_ofFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter_isRound
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.ofFilter_toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.RoundFilter

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

section Continuous

variable (hD : IsContinuousLattice D)

include hD

/-- Order-isomorphism: continuous lattice ↔ round `↟`-filters. -/
noncomputable def domainOrderIso : D ≃o RoundFilter (D := D) where
  toFun x := ⟨toFilter x, toFilter_isRound hD x⟩
  invFun f := ofFilter (D := D) f.1
  left_inv x := ofFilter_toFilter hD x
  right_inv f := Subtype.ext (toFilter_ofFilter f.2)
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      have : ofFilter (toFilter x) ≤ ofFilter (toFilter y) := by
        refine sSup_le fun a ha => ?_
        have ha' : a ≪ x := mem_wayBelowUp_toFilter.mp ha
        exact le_sSup (h (wayBelowUp a) ⟨a, ⟨rfl, ha'⟩⟩)
      simpa [ofFilter_toFilter hD] using this
    · intro hxy
      exact toFilter_mono hxy

end Continuous

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
