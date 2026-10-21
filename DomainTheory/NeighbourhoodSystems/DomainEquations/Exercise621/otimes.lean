/-ai
The smash product of two Scott systems is the Scott system whose neighbourhood system is the smash-product system of their underlying systems, using the proof that every neighbourhood of that system is nonempty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesTok_nonempty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The **smash product object** `𝒟₀ ⊗ 𝒟₁`. -/
def ScottSys.otimes (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨otimesTok A₀.sys A₁.sys, otimesTok_nonempty⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
