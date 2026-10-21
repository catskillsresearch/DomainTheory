/-ai
An element of the function space contains the enumerated neighbourhood of a code if and only if, whenever the consistency characteristic of the code equals 1, the element contains every step neighbourhood coded in the decoded list.

If the code is consistent, the enumerated set is the positive enumeration, and membership in the step-function neighbourhood is membership of every presented pair: each coded entry maps to its step pair, and every presented pair comes from a coded entry. If the code is inconsistent, the enumerated set is the negative enumeration; a demand that the characteristic equal 1 contradicts the case, and otherwise membership is the master-neighbourhood axiom of the function space.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)








































































































/-- **Bridge.** `φ ∋ Xenum c` iff, *when `c` is consistent*, `φ` contains every constituent step. -/
theorem mem_Xenum_iff (gN : ℕ → ℕ) (φ : (funSpace V₀ V₁).Element) (c : ℕ) :
    φ.mem (Xenum P₀ P₁ gN c) ↔
      (gN c = 1 → ∀ e ∈ decodeList c, φ.mem (step (P₀.X e.unpair.1) (P₁.X e.unpair.2))) := by
  by_cases h : gN c = 1
  · rw [Xenum_pos P₀ P₁ h, mem_stepFun_iff φ (funListOf_valid P₀ P₁ (decodeList c))]
    constructor
    · intro hp _ e he
      exact hp (funPair P₀ P₁ e) (List.mem_map.mpr ⟨e, he, rfl⟩)
    · intro himp p hp
      rw [funListOf, List.mem_map] at hp
      obtain ⟨e, he, rfl⟩ := hp
      exact himp h e he
  · rw [Xenum_neg P₀ P₁ h]
    constructor
    · intro _ hcon; exact absurd hcon h
    · intro _; rw [← funSpace_master]; exact φ.master_mem

end DomainTheory.NeighbourhoodSystems
