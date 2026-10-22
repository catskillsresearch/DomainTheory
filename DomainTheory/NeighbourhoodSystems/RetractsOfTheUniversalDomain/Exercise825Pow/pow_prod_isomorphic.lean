module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import Mathlib.Logic.Equiv.Nat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}


/-- **Exercise 8.25 (Scott 1981, PRG-19), first step: `𝒟^∞ × 𝒟^∞ ≅ 𝒟^∞`**, for any `𝒟`. Specialized
to `𝒟 = 𝒰` this is Scott's `𝒰^∞ × 𝒰^∞ ≅ 𝒰^∞`. -/
theorem pow_prod_isomorphic (V : NeighborhoodSystem α) :
    prod (iterSys V) (iterSys V) ≅ᴰ iterSys V :=
  ⟨powProdOrderIso V⟩

end DomainTheory.NeighbourhoodSystems
