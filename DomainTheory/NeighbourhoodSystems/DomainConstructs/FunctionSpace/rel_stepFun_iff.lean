/-ai
A map into a function space relates an input to a step intersection if and only if it relates that input to each step of the list.

The argument inducts on the list. The empty step neighborhood is the master of the function space, related by the master relation. A cons cell is the intersection of the head step and the tail. Monotonicity separates a relation to that intersection into the two factors, the tail is a neighborhood because the intersection is nonempty, and the inductive hypothesis handles the tail. In the other direction the two relations combine by right intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_cons
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.toApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_toFilter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_symm_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.leastMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.gSection_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curry_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- The relational generation lemma for maps `h : 𝒟₀ → (𝒟₁ → 𝒟₂)`: `X h (⋂ᵢ [Yᵢ,Zᵢ])` iff
`X h [Yᵢ,Zᵢ]` for all `i`. -/
theorem rel_stepFun_iff (h : ApproximableMap V₀ (funSpace V₁ V₂)) {X : Set α} (hX : V₀.mem X)
    {L : List (Set β × Set γ)} (hL : ∀ p ∈ L, V₁.mem p.1 ∧ V₂.mem p.2) :
    h.rel X (stepFun L) ↔ ∀ p ∈ L, h.rel X (step p.1 p.2) := by
  induction L with
  | nil =>
    simp only [stepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    show h.rel X (funSpace V₁ V₂).master
    exact h.rel_master hX
  | cons p L ih =>
    rw [stepFun_cons]
    have hp := hL p (List.mem_cons.mpr (Or.inl rfl))
    have hLtail : ∀ q ∈ L, V₁.mem q.1 ∧ V₂.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      have hne : (step p.1 p.2 ∩ stepFun L).Nonempty := (h.rel_cod hmem).2
      have hstep : h.rel X (step p.1 p.2) :=
        h.mono hmem subset_rfl Set.inter_subset_left hX (step_mem hp.1 hp.2)
      have htail : h.rel X (stepFun L) :=
        h.mono hmem subset_rfl Set.inter_subset_right hX
          ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : h.rel X (step p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : h.rel X (stepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact h.inter_right hstep htail

end DomainTheory.NeighbourhoodSystems
