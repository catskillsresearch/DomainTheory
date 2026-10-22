module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.EpsilonNFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat.catEps_mem_u3b5Closure_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}


variable (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂)


/-- **Closed form for `eval`.** After reading `x`, the reachable `inl`-states mirror `M₁.eval x`, and
the reachable `inr`-states are exactly the `M₂`-states reachable from some prefix-split `x = u ++ v`
with the `M₁`-prefix `u` accepted. This is the engine behind `catEps_accepts`. -/
theorem catEps_mem_eval_iff (x : List Bool) (s : σ₁ ⊕ σ₂) :
    s ∈ (catEps M₁ M₂).eval x ↔
      (∃ s₁, s = inl s₁ ∧ s₁ ∈ M₁.eval x) ∨
      (∃ t, s = inr t ∧ ∃ u v, x = u ++ v ∧ u ∈ M₁.accepts ∧ t ∈ M₂.eval v) := by
  induction x using List.reverseRecOn generalizing s with
  | nil =>
    show s ∈ (catEps M₁ M₂).εClosure (catEps M₁ M₂).start ↔ _
    rw [catEps_start, catEps_mem_εClosure_iff]
    constructor
    · rintro (hs | ⟨⟨q, hq, hqs⟩, hs⟩)
      · obtain ⟨s₁, hs₁, rfl⟩ := hs
        exact Or.inl ⟨s₁, rfl, hs₁⟩
      · obtain ⟨t, ht, rfl⟩ := hs
        refine Or.inr ⟨t, rfl, [], [], rfl, ?_, ht⟩
        obtain ⟨q', hq', hqq⟩ := hqs
        cases hqq
        exact ⟨q, hq, hq'⟩
    · rintro (⟨s₁, rfl, hs₁⟩ | ⟨t, rfl, u, v, hx, hu, hv⟩)
      · exact Or.inl ⟨s₁, hs₁, rfl⟩
      · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hx.symm
        obtain ⟨q, hq, hqstart⟩ := hu
        exact Or.inr ⟨⟨q, hq, q, hqstart, rfl⟩, t, hv, rfl⟩
  | append_singleton x a ih =>
    rw [εNFA.eval_append_singleton, εNFA.mem_stepSet_iff]
    constructor
    · rintro ⟨t, ht, hs⟩
      rw [ih] at ht
      rcases ht with ⟨s₁, rfl, hs₁⟩ | ⟨t₂, rfl, u, v, hx, hu, hv⟩
      · -- came from an `inl` state of `M₁`
        rw [catEps_step_inl_some, catEps_mem_εClosure_iff] at hs
        rcases hs with hs | ⟨⟨q, hq, hqmem⟩, hs⟩
        · -- still in `M₁`: extends the `inl` form
          obtain ⟨s', hs', rfl⟩ := hs
          exact Or.inl ⟨s', rfl, by rw [NFA.eval_append_singleton, NFA.mem_stepSet]; exact ⟨s₁, hs₁, hs'⟩⟩
        · -- `M₁` just reached an accept state on reading `a`: cross to `M₂` (split `v = []`)
          obtain ⟨q', hq', hqq⟩ := hqmem
          cases hqq
          obtain ⟨t', ht', rfl⟩ := hs
          refine Or.inr ⟨t', rfl, x ++ [a], [], (List.append_nil _).symm, ?_, ht'⟩
          rw [NFA.mem_accepts]
          refine ⟨q, hq, ?_⟩
          change q ∈ M₁.eval (x ++ [a])
          rw [NFA.eval_append_singleton, NFA.mem_stepSet]
          exact ⟨s₁, hs₁, hq'⟩
      · -- came from an `inr` state of `M₂`: extends the `inr` form (split `v ↦ v ++ [a]`)
        rw [catEps_step_inr_some, catEps_mem_εClosure_iff] at hs
        rcases hs with hs | ⟨⟨q, _, hqmem⟩, _⟩
        · obtain ⟨t', ht', rfl⟩ := hs
          refine Or.inr ⟨t', rfl, u, v ++ [a], by rw [hx, List.append_assoc], hu, ?_⟩
          rw [NFA.eval_append_singleton, NFA.mem_stepSet]; exact ⟨t₂, hv, ht'⟩
        · exact absurd hqmem (by simp)
    · rintro (⟨s', rfl, hs'⟩ | ⟨t', rfl, u, v, hx, hu, hv⟩)
      · -- `inl` form: step `M₁` one more
        rw [NFA.eval_append_singleton, NFA.mem_stepSet] at hs'
        obtain ⟨s₁, hs₁, hstep⟩ := hs'
        exact ⟨inl s₁, (ih (inl s₁)).mpr (Or.inl ⟨s₁, rfl, hs₁⟩),
          by rw [catEps_step_inl_some, catEps_mem_εClosure_iff]; exact Or.inl ⟨s', hstep, rfl⟩⟩
      · -- `inr` form: the split `x ++ [a] = u ++ v`; cases on whether `v` is empty
        rcases List.eq_nil_or_concat v with rfl | ⟨v', c, rfl⟩
        · -- `v = []`: `u = x ++ [a] ∈ L₁`; cross via the ε-edge after reading `a`
          rw [List.append_nil] at hx; subst hx
          rw [NFA.mem_accepts] at hu
          obtain ⟨q, hq, hqe⟩ := hu
          change q ∈ M₁.eval (x ++ [a]) at hqe
          rw [NFA.eval_append_singleton, NFA.mem_stepSet] at hqe
          obtain ⟨s₁, hs₁, hstep⟩ := hqe
          refine ⟨inl s₁, (ih (inl s₁)).mpr (Or.inl ⟨s₁, rfl, hs₁⟩), ?_⟩
          rw [catEps_step_inl_some, catEps_mem_εClosure_iff]
          exact Or.inr ⟨⟨q, hq, q, hstep, rfl⟩, t', hv, rfl⟩
        · -- `v = v' ++ [c]`: necessarily `c = a`, `x = u ++ v'`; step `M₂` one more
          rw [List.concat_eq_append] at hx hv
          rw [← List.append_assoc] at hx
          obtain ⟨hxe, hac⟩ := List.append_inj' hx rfl
          have hca : c = a := by simpa using hac.symm
          subst hca
          rw [NFA.eval_append_singleton, NFA.mem_stepSet] at hv
          obtain ⟨t₂, ht₂, hstep⟩ := hv
          refine ⟨inr t₂, (ih (inr t₂)).mpr (Or.inr ⟨t₂, rfl, u, v', hxe, hu, ht₂⟩), ?_⟩
          rw [catEps_step_inr_some, catEps_mem_εClosure_iff]
          exact Or.inl ⟨t', hstep, rfl⟩

end Exercise722
end DomainTheory.NeighbourhoodSystems
