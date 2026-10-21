/-ai
The master of the domain system and the master of the codomain system generate each other.

The two relations are the master relations of the forward and backward approximable maps.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.IsGen
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Basic.notation4

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- The masters generate each other: `IsGen Δ_D Δ_E` (from `i.master_rel`, `j.master_rel`). -/
theorem isGen_master : IsGen i j D.master E.master :=
  ⟨i.master_rel, j.master_rel⟩

end ProjectionPair

end DomainTheory.NeighbourhoodSystems
