module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A proper product neighbourhood is a neighbourhood of the smash. -/
theorem smash_mem_proper {X : Set α} {Y : Set β} (hX : V₀.mem X) (hXne : X ≠ V₀.master)
    (hY : V₁.mem Y) (hYne : Y ≠ V₁.master) : (smash V₀ V₁).mem (prodNbhd X Y) :=
  Or.inr ⟨X, Y, hX, hXne, hY, hYne, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise510
