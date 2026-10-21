/-ai
The identity map is strict.

Unpack the relation witness. Antisymmetry of inclusion, using that the witnessed neighbourhood lies in the master and that the witness supplies the other inclusion, shows that the output equals the master.
ai-/
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
