module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}



variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}






















/-- The identity is strict. -/
theorem isStrict_idMap : IsStrict (idMap V₀) := by
  rintro Y ⟨_, hY, hsub⟩
  exact Set.Subset.antisymm (V₀.sub_master hY) hsub

end DomainTheory.NeighbourhoodSystems.Exercise510
