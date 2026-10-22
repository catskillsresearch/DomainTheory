module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.IsStrict

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The strict maps `𝒟₀ →⊥ 𝒟₁`, as a subtype carrying the inherited approximation order. -/
abbrev StrictMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :=
  {f : ApproximableMap V₀ V₁ // IsStrict f}

end DomainTheory.NeighbourhoodSystems.Exercise510
