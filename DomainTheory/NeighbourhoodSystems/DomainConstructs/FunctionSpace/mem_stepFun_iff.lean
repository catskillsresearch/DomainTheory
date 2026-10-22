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

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The "generation" lemma: a filter contains the intersection `stepFun L` iff it contains each
step `[Xᵢ, Yᵢ]`. (The step sets `[X, Y] ∈ φ` generate the filter `φ`.) -/
theorem mem_stepFun_iff (φ : (funSpace V₀ V₁).Element) {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) :
    φ.mem (stepFun L) ↔ ∀ p ∈ L, φ.mem (step p.1 p.2) := by
  induction L with
  | nil => simp only [stepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
           exact φ.master_mem
  | cons p L ih =>
    rw [stepFun_cons]
    have hp := hL p (List.mem_cons.mpr (Or.inl rfl))
    have hLtail : ∀ q ∈ L, V₀.mem q.1 ∧ V₁.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      have hstep : φ.mem (step p.1 p.2) :=
        φ.up_mem hmem (step_mem hp.1 hp.2) Set.inter_subset_left
      have hne : (step p.1 p.2 ∩ stepFun L).Nonempty := (φ.sub hmem).2
      have htail : φ.mem (stepFun L) :=
        φ.up_mem hmem ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩ Set.inter_subset_right
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : φ.mem (step p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : φ.mem (stepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact φ.inter_mem hstep htail

end DomainTheory.NeighbourhoodSystems
