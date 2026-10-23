module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset_empty

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

/-- Empty set does not entail top (no derivation bottoms out). -/
theorem not_VEnt_empty_top : ¬ VEnt (∅ : Finset VToken) .top := by
  have aux : ∀ {u : Finset VToken} {c : VToken},
      VEnt u c → c = .top → u = ∅ → False := by
    intro u c h
    induction h with
    | bot => intro hc; exact nomatch hc
    | top_mem hm =>
      intro _ hu; exact Finset.notMem_empty _ (hu ▸ hm)
    | top_both _ _ ihL _ =>
      intro _ hu
      exact ihL rfl (by rw [hu]; exact vPairLFinset_empty)
    | pairL_top => intro hc; exact nomatch hc
    | pairL_proj => intro hc; exact nomatch hc
    | pairR_top => intro hc; exact nomatch hc
    | pairR_proj => intro hc; exact nomatch hc
  exact fun h => aux h rfl rfl

end InfoSys

end DomainTheory.InformationSystems
