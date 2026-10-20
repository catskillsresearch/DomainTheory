module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}



variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}





theorem smash_mem_iff {W : Set (α ⊕ β)} :
    (smash V₀ V₁).mem W ↔
      W = prodNbhd V₀.master V₁.master ∨ SmashProper V₀ V₁ W := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise510
