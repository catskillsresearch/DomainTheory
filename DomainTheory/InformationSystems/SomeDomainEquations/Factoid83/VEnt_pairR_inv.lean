module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem VEnt_pairR_inv {v : Finset VToken} {y : VToken}
    (h : VEnt v (.pairR y)) : .top ∈ v ∨ VEnt (vPairRFinset v) y := by
  cases h with
  | pairR_top hm => exact Or.inl hm
  | pairR_proj h' => exact Or.inr h'

end InfoSys

end DomainTheory.InformationSystems
