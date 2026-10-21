/-ai
Currying relates an indexed neighbourhood to an enumerated function-space neighbourhood if and only if, whenever the code is consistent, the original map relates the product of that neighbourhood with each selected input to the corresponding output.

Unfold currying. In one direction, read membership of the section map in the enumeration and rewrite the section relation as the product relation. In the other direction, the indexed neighbourhood and the enumerated set are neighbourhoods, and the same rewriting puts the section map in the enumeration.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.mem_Xenum_iff_map

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


/-- **Bridge for `curry`.** `(X₀ₙ) curry(g) (Xenum c)` iff, *when `c` is consistent*, `g` relates
`X₀ₙ ∪ X₁_{e.1}` to `X₂_{e.2}` for every coded entry `e`. -/
theorem curry_rel_Xenum_iff {V₂ : NeighborhoodSystem γ} (P₂ : ComputablePresentation V₂)
    (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₁ P₂ (decodeList c))
      : Set (ApproximableMap V₁ V₂)).Nonempty)
    (g : ApproximableMap (prod V₀ V₁) V₂) (n c : ℕ) :
    (curry g).rel (P₀.X n) (Xenum P₁ P₂ gN c) ↔
      (gN c = 1 → ∀ e ∈ decodeList c,
        g.rel (prodNbhd (P₀.X n) (P₁.X e.unpair.1)) (P₂.X e.unpair.2)) := by
  rw [curry_rel]
  constructor
  · rintro ⟨hX, _, hmem⟩
    rw [mem_Xenum_iff_map P₁ P₂ gN (gSection g hX) c] at hmem
    intro hc e he
    have hrel := hmem hc e he
    rwa [gSection_rel] at hrel
  · intro himp
    refine ⟨P₀.mem_X n, Xenum_mem P₁ P₂ gN hgN c, ?_⟩
    rw [mem_Xenum_iff_map P₁ P₂ gN (gSection g (P₀.mem_X n)) c]
    intro hc e he
    rw [gSection_rel]
    exact himp hc e he

end DomainTheory.NeighbourhoodSystems
