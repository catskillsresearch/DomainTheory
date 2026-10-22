module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.EpsilonNFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat.catEps

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}


variable (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂)

@[simp] theorem catEps_step_inl_some (s : σ₁) (c : Bool) :
    (catEps M₁ M₂).step (inl s) (some c) = inl '' M₁.step s c := rfl
@[simp] theorem catEps_step_inl_none (s : σ₁) :
    (catEps M₁ M₂).step (inl s) none = {t | s ∈ M₁.accept ∧ t ∈ inr '' M₂.start} := rfl
@[simp] theorem catEps_step_inr_some (s : σ₂) (c : Bool) :
    (catEps M₁ M₂).step (inr s) (some c) = inr '' M₂.step s c := rfl
@[simp] theorem catEps_step_inr_none (s : σ₂) :
    (catEps M₁ M₂).step (inr s) none = ∅ := rfl
@[simp] theorem catEps_start : (catEps M₁ M₂).start = inl '' M₁.start := rfl
@[simp] theorem catEps_accept : (catEps M₁ M₂).accept = inr '' M₂.accept := rfl

example [Fintype σ₁] [Fintype σ₂] : Fintype (σ₁ ⊕ σ₂) := inferInstance
end Exercise722
end DomainTheory.NeighbourhoodSystems
