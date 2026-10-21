/-ai
An approximable map is strict when it relates the master neighbourhood of its domain only to the master neighbourhood of its codomain. This is the relational form of sending the bottom element to the bottom element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **A map is *strict* when `f(⊥) = ⊥`.** Relationally: `f` sends the master input only to the master
output. -/
def IsStrict (f : ApproximableMap V₀ V₁) : Prop :=
  ∀ ⦃Y⦄, f.rel V₀.master Y → Y = V₁.master

end DomainTheory.NeighbourhoodSystems.Exercise510
