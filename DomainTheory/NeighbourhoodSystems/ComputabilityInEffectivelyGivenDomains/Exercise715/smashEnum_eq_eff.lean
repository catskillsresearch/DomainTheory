/-ai
Given deciders of properness with values in {0, 1}, the smash enumeration of a code equals the product of the component neighbourhoods at the effective indices, which select the raw index when the product of the decider values is 1 and the master index when that product is 0.

If both factors are proper, both deciders equal 1, selection returns the raw indices, and the enumeration is their product. Otherwise the product of the decider values is 0, because a failing decider is 0, selection returns the master indices, and both sides are the product of the masters.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_proper
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

/-- **The smash enumeration as a product neighbourhood with *effective* factors.** Given `{0,1}`
deciders `c₀`, `c₁` of properness, `smashEnum t = prodNbhd X⁰_{effL} X¹_{effR}` where the effective
index `effL = (proper? t.1 : masterIdx₀)` is computed primitively by `selectFn`. This is the bridge
that turns the smash relations into the components' relations on the effective indices. -/
theorem smashEnum_eq_eff {c₀ c₁ : ℕ → ℕ} (hc₀le : ∀ n, c₀ n ≤ 1) (hc₁le : ∀ n, c₁ n ≤ 1)
    (hc₀ : ∀ n, P₀.X n ≠ V₀.master ↔ c₀ n = 1) (hc₁ : ∀ n, P₁.X n ≠ V₁.master ↔ c₁ n = 1) (t : ℕ) :
    smashEnum P₀ P₁ t =
      prodNbhd (P₀.X (selectFn (c₀ t.unpair.1 * c₁ t.unpair.2) t.unpair.1 P₀.masterIdx))
        (P₁.X (selectFn (c₀ t.unpair.1 * c₁ t.unpair.2) t.unpair.2 P₁.masterIdx)) := by
  by_cases h : P₀.X t.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2 ≠ V₁.master
  · have e0 : c₀ t.unpair.1 = 1 := (hc₀ _).mp h.1
    have e1 : c₁ t.unpair.2 = 1 := (hc₁ _).mp h.2
    rw [smashEnum_proper h, e0, e1, mul_one, selectFn_one, selectFn_one]
  · rw [smashEnum_master h]
    have hpf : c₀ t.unpair.1 * c₁ t.unpair.2 = 0 := by
      rcases not_and_or.mp h with h0 | h1
      · have hz : c₀ t.unpair.1 = 0 := by
          have hle := hc₀le t.unpair.1
          rcases (show c₀ t.unpair.1 = 0 ∨ c₀ t.unpair.1 = 1 by omega) with h | h
          · exact h
          · exact absurd ((hc₀ _).mpr h) h0
        rw [hz, Nat.zero_mul]
      · have hz : c₁ t.unpair.2 = 0 := by
          have hle := hc₁le t.unpair.2
          rcases (show c₁ t.unpair.2 = 0 ∨ c₁ t.unpair.2 = 1 by omega) with h | h
          · exact h
          · exact absurd ((hc₁ _).mpr h) h1
        rw [hz, Nat.mul_zero]
    rw [hpf, selectFn_zero, selectFn_zero, P₀.masterIdx_spec, P₁.masterIdx_spec]

end Smash

end DomainTheory.NeighbourhoodSystems
