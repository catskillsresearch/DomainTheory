/-ai
From an entailment of a right pair (Δ, Y), either top belongs to the premise or the right pair projection of the premise entails Y.

Case analysis on the derivation gives the first alternative from the top-membership clause and the second from the projection clause.
ai-/
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

theorem VEnt_pairR_inv {v : Finset VToken} {y : VToken}
    (h : VEnt v (.pairR y)) : .top ∈ v ∨ VEnt (vPairRFinset v) y := by
  cases h with
  | pairR_top hm => exact Or.inl hm
  | pairR_proj h' => exact Or.inr h'

end InfoSys

end DomainTheory.InformationSystems
