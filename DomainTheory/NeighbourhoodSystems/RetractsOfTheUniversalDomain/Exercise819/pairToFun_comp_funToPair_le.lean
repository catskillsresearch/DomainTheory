module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.swapProdT
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.pairToFun
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.funToPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.sumToProdT
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.TD_trichotomy
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.toApproxMap_pairToFun
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.toElementMap_funToPair

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_false
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
