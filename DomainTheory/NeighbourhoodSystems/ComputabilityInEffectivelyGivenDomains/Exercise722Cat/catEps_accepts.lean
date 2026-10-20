module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.EpsilonNFA
import all Mathlib.Computability.EpsilonNFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat.catEps_mem_eval_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}


variable (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂)


/-- **The concatenation automaton recognises exactly the concatenation language.** -/
theorem catEps_accepts :
    (catEps M₁ M₂).accepts = concat M₁.accepts M₂.accepts := by
  ext x
  constructor
  · rintro ⟨S, hS, hSeval⟩
    obtain ⟨t, ht, rfl⟩ := hS
    rw [catEps_mem_eval_iff] at hSeval
    rcases hSeval with ⟨s₁, hc, _⟩ | ⟨t', heq, u, v, hx, hu, hv⟩
    · exact absurd hc (by simp)
    · cases heq
      exact ⟨u, hu, v, ⟨t, ht, hv⟩, hx.symm⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨t, ht, hteval⟩ := hv
    refine ⟨inr t, ⟨t, ht, rfl⟩, ?_⟩
    rw [catEps_mem_eval_iff]
    exact Or.inr ⟨t, rfl, u, v, rfl, hu, hteval⟩

end Exercise722
end DomainTheory.NeighbourhoodSystems
