/-ai
If two self-maps of the universal domain are retractions, then so is their sum combinator.

Compare elements, and split on whether the sum extraction of the element meets the left copy, the right copy, or only the master. On the left, the left-case formula, the identity that the sum extraction after the sum injection is the identity, and the fact that the left injection meets the left copy again, return to the left case; the left extraction after the left injection is the identity, and the first map is idempotent on elements. The right case is the same argument with the second map and the right injection and extraction. On a point that meets only the master, the master-case formula sends the element to bottom, and the sum extraction of bottom is bottom, which still meets only the master, so the same formula applies again.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_of_comp_eq_idMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_idem_of_isRetraction
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.inMapu2080_toElementMap_reaches_left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.inMapu2081_toElementMap_reaches_right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.jPlus_bot_eq_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_sumComb_of_left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_sumComb_of_right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_sumComb_of_neither

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


/-- **Proposition 8.10, `+`-case, retraction half.** -/
theorem isRetraction_sumComb {a b : ApproximableMap U U} (ha : Retraction a)
    (hb : Retraction b) : Retraction (sumComb a b) := by
  constructor
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  rcases sum_element_trichotomy (jPlus.toElementMap x) with hL | hR | hN
  · rw [toElementMap_sumComb_of_left hL]
    set v := a.toElementMap (outMap₀.toElementMap (jPlus.toElementMap x)) with hv
    have hjy : jPlus.toElementMap (iPlus.toElementMap (inMap₀.toElementMap v))
        = inMap₀.toElementMap v := toElementMap_of_comp_eq_idMap jPlus_comp_iPlus _
    have hLy : ∃ X, U.mem X ∧
        (jPlus.toElementMap (iPlus.toElementMap (inMap₀.toElementMap v))).mem (inj₀ X) := by
      rw [hjy]; exact inMap₀_toElementMap_reaches_left v
    rw [toElementMap_sumComb_of_left hLy, hjy,
      toElementMap_of_comp_eq_idMap outMap₀_comp_inMap₀ v, toElementMap_idem_of_isRetraction ha]
  · rw [toElementMap_sumComb_of_right hR]
    set v := b.toElementMap (outMap₁.toElementMap (jPlus.toElementMap x)) with hv
    have hjy : jPlus.toElementMap (iPlus.toElementMap (inMap₁.toElementMap v))
        = inMap₁.toElementMap v := toElementMap_of_comp_eq_idMap jPlus_comp_iPlus _
    have hRy : ∃ Y, U.mem Y ∧
        (jPlus.toElementMap (iPlus.toElementMap (inMap₁.toElementMap v))).mem (inj₁ Y) := by
      rw [hjy]; exact inMap₁_toElementMap_reaches_right v
    rw [toElementMap_sumComb_of_right hRy, hjy,
      toElementMap_of_comp_eq_idMap outMap₁_comp_inMap₁ v, toElementMap_idem_of_isRetraction hb]
  · rw [toElementMap_sumComb_of_neither hN]
    apply toElementMap_sumComb_of_neither
    intro W hW
    rw [jPlus_bot_eq_bot, mem_bot] at hW
    exact hW

end DomainTheory.NeighbourhoodSystems
