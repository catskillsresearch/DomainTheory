/-ai
A point lies in the intersection of relevant outputs if and only if it lies in the master and in every output whose input contains the given set.

The argument inducts on the list. The empty intersection is membership in the master. For a head and a tail, the unfolded intersection splits into the head constraint and the tail, and the quantifier over the cons cell splits into the head pair and the pairs of the tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.toApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_toFilter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_symm_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_cons

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Membership in `interYs`: `z ∈ ⋂{Yᵢ ∣ X ⊆ Xᵢ}` iff `z ∈ Δ₁` and `z ∈ Yᵢ` for every `i` with
`X ⊆ Xᵢ`. -/
theorem mem_interYs {m : Set β} {L : List (Set α × Set β)} {X : Set α} {z : β} :
    z ∈ interYs m L X ↔ z ∈ m ∧ ∀ p ∈ L, X ⊆ p.1 → z ∈ p.2 := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [interYs_cons]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ih, List.mem_cons]
    constructor
    · rintro ⟨hp, hm, hL⟩
      refine ⟨hm, ?_⟩
      rintro q (rfl | hq) hXq
      · exact hp hXq
      · exact hL q hq hXq
    · rintro ⟨hm, hall⟩
      exact ⟨fun hXp => hall p (Or.inl rfl) hXp, hm,
        fun q hq hXq => hall q (Or.inr hq) hXq⟩

end DomainTheory.NeighbourhoodSystems
