module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.StrictMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_append
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_master_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Intersection of two neighbourhoods, when non-empty, is again one. -/
theorem strictFun_mem_inter {W W' : Set (StrictMap V₀ V₁)}
    (hW : (strictFun V₀ V₁).mem W) (hW' : (strictFun V₀ V₁).mem W') (hne : (W ∩ W').Nonempty) :
    (strictFun V₀ V₁).mem (W ∩ W') := by
  obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
  obtain ⟨⟨L', hL', rfl⟩, _⟩ := hW'
  refine ⟨⟨L ++ L', ?_, (sstepFun_append _ _).symm⟩, hne⟩
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hL' p h

end DomainTheory.NeighbourhoodSystems.Exercise510
