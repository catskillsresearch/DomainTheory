/-ai
This file introduces the instance that there is a unique approximable map into the one-point domain. The default map is the constant map at the default element, and every map equals it because there is at most one such map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise323.BasicInst4

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} (V : NeighborhoodSystem α)

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 3.23 (Scott 1981, PRG-19).** `𝟙 = unitSys` is the *terminal object*: for every domain
`𝒟` there is a unique approximable mapping `𝒟 → 𝟙` (the constant map at `⊥`). -/
instance : Unique (ApproximableMap V unitSys) where
  default := constMap V (default : unitSys.Element)
  uniq _ := Subsingleton.elim _ _

end DomainTheory.NeighbourhoodSystems
