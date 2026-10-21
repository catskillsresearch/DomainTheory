/-ai
The composite of the curried pairing after the map that reads a function at true and at false lies below the identity on the function space from the three-point domain to E. Feeding those two values back through the conditional agrees with the function at true and at false, and lies below it at bottom.

Compare the maps on elements and pass across the function-space equivalence. Split the argument into bottom, true, and false. At bottom the conditional is the bottom of E, which lies below every value. At true and at false the conditional returns the corresponding component of the pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.TD_trichotomy
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.toApproxMap_pairToFun
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.toElementMap_funToPair

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u






section Prod

variable {α : Type u} {E : NeighborhoodSystem α}




/-- **`pairToFun ∘ funToPair ≤ I`.** For every `φ : T → E`, feeding `(φ(true), φ(false))` back
through `cond` gives a map agreeing with `φ` at `true`/`false` and `≤ φ` at `⊥` (`E.bot ≤`
anything). Case split on `T`'s three elements (`TD_trichotomy`). -/
theorem pairToFun_comp_funToPair_le :
    (pairToFun (E := E)).comp funToPair ≤ idMap (funSpace TD E) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_funToPair]
  apply (funSpaceEquiv TD E).map_rel_iff.mp
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, le_iff_toElementMap_le]
  intro t
  rcases TD_trichotomy t with rfl | rfl | rfl
  · rw [toApproxMap_pairToFun, Exercise326.cond_bot]; exact E.bot_le _
  · rw [toApproxMap_pairToFun, Exercise326.cond_true]
  · rw [toApproxMap_pairToFun, Exercise326.cond_false]

end Prod
end DomainTheory.NeighbourhoodSystems
