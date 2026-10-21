/-ai
The function space of two neighborhood systems has approximable maps as tokens. A set of maps is a neighborhood when it is nonempty and equals the step neighborhood of a finite list of neighborhood pairs. The master is the set of all maps, inhabited by the constant map at the bottom element. The intersection of two such neighborhoods, when the candidate intersection is nonempty, is the step neighborhood of the appended lists. Every neighborhood is contained in the set of all maps.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_append
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Definition 3.8 (Scott 1981, PRG-19).** The *function space* `(𝒟₀ → 𝒟₁)`: tokens are
approximable maps, neighbourhoods are non-empty finite intersections of step sets. -/
def funSpace (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    NeighborhoodSystem (ApproximableMap V₀ V₁) where
  mem W := (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = stepFun L)
    ∧ W.Nonempty
  master := Set.univ
  master_nonempty := ⟨constMap V₀ V₁.bot, Set.mem_univ _⟩
  master_mem := ⟨⟨[], by simp, stepFun_nil.symm⟩, ⟨constMap V₀ V₁.bot, Set.mem_univ _⟩⟩
  inter_mem := by
    rintro W W' Z ⟨⟨L, hL, rfl⟩, _⟩ ⟨⟨L', hL', rfl⟩, _⟩ ⟨_, hZne⟩ hZsub
    refine ⟨⟨L ++ L', ?_, (stepFun_append _ _).symm⟩, hZne.mono hZsub⟩
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hL p h
    · exact hL' p h
  sub_master := fun _ => Set.subset_univ _

end DomainTheory.NeighbourhoodSystems
