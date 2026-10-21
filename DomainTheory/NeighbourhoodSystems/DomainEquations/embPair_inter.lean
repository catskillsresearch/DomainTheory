/-ai
The intersection of two pair embeddings is the pair embedding of the componentwise intersections.

Compare a tagged point. On the empty path both membership conditions fail. On a cons cell the head bit selects the component, and equality of cons cells identifies the tails with the intersections.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embPair_inter (P Q P' Q' : Set (List Bool × α)) :
    embPair P Q ∩ embPair P' Q' = embPair (P ∩ P') (Q ∩ Q') := by
  ext ⟨p, a⟩
  simp only [Set.mem_inter_iff, mem_embPair]
  rcases p with _ | ⟨b, ps⟩
  · simp
  · cases b <;> simp [List.cons.injEq]

end Example61

end DomainTheory.NeighbourhoodSystems
