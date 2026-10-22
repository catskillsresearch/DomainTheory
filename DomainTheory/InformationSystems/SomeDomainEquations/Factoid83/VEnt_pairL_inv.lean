module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

/-- From `v ⊢ (X, Δ)`, either `∇ ∈ v` or the left projection entails `X`. -/
theorem VEnt_pairL_inv {v : Finset VToken} {x : VToken}
    (h : VEnt v (.pairL x)) : .top ∈ v ∨ VEnt (vPairLFinset v) x := by
  cases h with
  | pairL_top hm => exact Or.inl hm
  | pairL_proj h' => exact Or.inr h'

end InfoSys

end DomainTheory.InformationSystems
