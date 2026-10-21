/-ai
The step-function set of a pair followed by a list is the intersection of the step set of that pair with the step-function set of the list.

Extensionality and the membership criteria reduce the equality to the decomposition of a cons cell: the head pair gives the step, and the remaining pairs give the step-function set of the tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.StrictMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem sstepFun_cons (p : Set α × Set β) (L : List (Set α × Set β)) :
    (sstepFun (p :: L) : Set (StrictMap V₀ V₁)) = sstep p.1 p.2 ∩ sstepFun L := by
  ext f
  simp only [mem_sstepFun, List.mem_cons, Set.mem_inter_iff, mem_sstep]
  constructor
  · intro h; exact ⟨h p (Or.inl rfl), fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨hp, hrest⟩ q (rfl | hq)
    · exact hp
    · exact hrest q hq

end DomainTheory.NeighbourhoodSystems.Exercise510
