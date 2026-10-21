/-ai
The step-function set of a concatenated list is the intersection of the step-function sets of the two lists.

Extensionality and the membership criterion reduce the equality to quantification over the concatenated list. A map that relates every pair of the concatenation relates every pair of each half, and a map that relates every pair of each half relates a pair of the concatenation according to which half contains it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.StrictMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem sstepFun_append (L L' : List (Set α × Set β)) :
    (sstepFun (L ++ L') : Set (StrictMap V₀ V₁)) = sstepFun L ∩ sstepFun L' := by
  ext f
  simp only [mem_sstepFun, List.mem_append, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨hL, hL'⟩ p (hp | hp)
    · exact hL p hp
    · exact hL' p hp

end DomainTheory.NeighbourhoodSystems.Exercise510
