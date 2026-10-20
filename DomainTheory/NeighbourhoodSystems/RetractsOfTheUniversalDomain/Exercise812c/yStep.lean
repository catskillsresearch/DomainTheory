module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.splitChoice'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xyStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **The `Y`-sub-step**, symmetric to `xStep`: split `D₀`'s side while directly refining `D₁`'s
side. The `.swap` puts the output back into `(α-side, β-side)` order, matching `atomPair`'s own
`(A2, B2)` convention (`xyStep`'s first component is always the *direct* side, which for the
`Y`-sub-step is the `β`-side). -/
noncomputable def yStep {α β : Type*} (D₀ : NeighborhoodSystem α) (hD₀nomin : D₀.NoMinimal)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : Set α × Set β :=
  (xyStep (splitChoice' D₀ hD₀nomin) B1 A1 Yn b).swap

end DomainTheory.NeighbourhoodSystems
