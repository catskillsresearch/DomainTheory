module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset_mono

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem VEnt_mono {u v : Finset VToken} {c : VToken}
    (huv : u ⊆ v) (h : VEnt u c) : VEnt v c := by
  induction h generalizing v with
  | bot => exact VEnt.bot
  | top_mem hm => exact VEnt.top_mem (huv hm)
  | top_both _ _ ihL ihR =>
    exact VEnt.top_both (ihL (vPairLFinset_mono huv)) (ihR (vPairRFinset_mono huv))
  | pairL_top hm => exact VEnt.pairL_top (huv hm)
  | pairL_proj _ ih => exact VEnt.pairL_proj (ih (vPairLFinset_mono huv))
  | pairR_top hm => exact VEnt.pairR_top (huv hm)
  | pairR_proj _ ih => exact VEnt.pairR_proj (ih (vPairRFinset_mono huv))

end InfoSys

end DomainTheory.InformationSystems
