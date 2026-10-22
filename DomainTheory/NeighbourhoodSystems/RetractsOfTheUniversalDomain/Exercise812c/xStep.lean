module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.splitChoice'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xyStep

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **The `X`-sub-step**, as an instance of `xyStep`: split `D₁`'s side while directly refining
`D₀`'s side. -/
noncomputable def xStep {α β : Type*} (D₁ : NeighborhoodSystem β) (hD₁nomin : D₁.NoMinimal)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : Set α × Set β :=
  xyStep (splitChoice' D₁ hD₁nomin) A B Xn b

end DomainTheory.NeighbourhoodSystems
