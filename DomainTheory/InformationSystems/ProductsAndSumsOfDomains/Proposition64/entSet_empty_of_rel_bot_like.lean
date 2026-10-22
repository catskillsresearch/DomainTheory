module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.subset_botElement_of_projections_empty

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

variable {C : InfoSys γ}


theorem entSet_empty_of_rel_bot_like (h : ApproximableMap (sumSystem A B) C)
    (hbot : h.toElement (sumSystem A B).botElement = C.botElement)
    {u : Finset (SumToken α β)} {s : Finset γ}
    (hu : SumCon A B u) (hs : s ∈ C.Con) (hl : lftFinset u = ∅) (hr : rhtFinset u = ∅)
    (hh : h.rel u s) : C.EntSet ∅ s := by
  have hsub := subset_botElement_of_projections_empty A B hl hr
  have hcl : (sumSystem A B).closure u hu ≤ (sumSystem A B).botElement := by
    intro p hp
    exact (sumSystem A B).botElement.closed u p hsub hp
  have hle : C.closure s hs ≤ C.botElement := by
    have := (h.rel_iff_closure_le hu hs).1 hh
    have := le_trans this (toElement_mono h hcl)
    rwa [hbot] at this
  intro Y hY
  have hY' : Y ∈ (C.closure s hs).carrier := C.subset_closure hs hY
  have hbotY : Y ∈ C.botElement.carrier := hle hY'
  exact C.ent_trans C.con_empty (C.con_sing C.bot)
    (fun _ hz => by
      have : _ = C.bot := Finset.mem_singleton.mp hz
      subst this; exact C.ent_bot C.con_empty)
    hbotY

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
