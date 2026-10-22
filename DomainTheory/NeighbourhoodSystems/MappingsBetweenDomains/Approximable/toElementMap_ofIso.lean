module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Theorem 2.7 — the relation re-defines the function.** The elementwise map of `ofIso e` is `e`
itself: `(ofIso e)(x) = e(x)` for every `x`. The forward inclusion uses that `X ∈ x` implies
`↑X ⊑ x`, hence `e(↑X) ⊑ e(x)`; the reverse uses surjectivity of `e` (via `e.symm`) exactly as in
Scott's proof — one shows `x = e⁻¹((ofIso e)(x))` by antisymmetry. -/
theorem toElementMap_ofIso (e : V₀.Element ≃o V₁.Element) (x : V₀.Element) :
    (ofIso e).toElementMap x = e x := by
  have hgxle : (ofIso e).toElementMap x ≤ e x := by
    rintro Y ⟨X, hXx, hX, hY⟩
    have hpx : V₀.principal hX ≤ x := fun Z hZ => x.up_mem hXx hZ.1 hZ.2
    exact (e.monotone hpx) Y hY
  have key : x = e.symm ((ofIso e).toElementMap x) := by
    apply le_antisymm
    · intro X hXx
      have hX : V₀.mem X := x.sub hXx
      have hsub : e (V₀.principal hX) ≤ (ofIso e).toElementMap x :=
        fun Y hY => ⟨X, hXx, hX, hY⟩
      have hple : V₀.principal hX ≤ e.symm ((ofIso e).toElementMap x) := by
        have h := e.symm.monotone hsub
        rwa [e.symm_apply_apply] at h
      exact hple X ⟨hX, subset_rfl⟩
    · have h := e.symm.monotone hgxle
      rwa [e.symm_apply_apply] at h
  have h1 : e x = e (e.symm ((ofIso e).toElementMap x)) := congrArg e key
  rw [e.apply_symm_apply] at h1
  exact h1.symm

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
