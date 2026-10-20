module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.IsStrict

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Strictness is downward closed: a map below a strict map is strict. -/
theorem IsStrict.mono {f g : ApproximableMap V₀ V₁} (hf : IsStrict f) (hgf : g ≤ f) : IsStrict g :=
  fun _ hrel => hf (hgf _ _ hrel)

end DomainTheory.NeighbourhoodSystems.Exercise510
