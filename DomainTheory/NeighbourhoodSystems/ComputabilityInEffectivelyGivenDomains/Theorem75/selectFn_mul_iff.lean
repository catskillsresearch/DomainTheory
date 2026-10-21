/-ai
Selection of a second bit against 0 on a first bit equals 1 if and only if both bits equal 1.

That selection equals the product of the two bits, and a product of natural numbers equals 1 precisely when both factors equal 1.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- `selectFn c d 0 = 1` decides the conjunction `c = 1 ∧ d = 1`. -/
theorem selectFn_mul_iff (c d : ℕ) : selectFn c d 0 = 1 ↔ c = 1 ∧ d = 1 := by
  have h : selectFn c d 0 = c * d := by simp only [selectFn, Nat.mul_zero, Nat.add_zero]
  rw [h, nat_mul_eq_one]

end DomainTheory.NeighbourhoodSystems
