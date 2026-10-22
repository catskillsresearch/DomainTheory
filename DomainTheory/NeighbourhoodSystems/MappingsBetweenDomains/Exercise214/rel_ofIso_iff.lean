module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise214.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise214.phi_spec

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Exercise 2.14 — the approximable mapping of `e` is `φ(X) ⊆ Y`.** For `X ∈ 𝒟₀`,
`(ofIso e).rel X Y ↔ Y ∈ 𝒟₁ ∧ φ(X) ⊆ Y`. (Immediate from `phi_spec` and `mem_principal`.) -/
theorem rel_ofIso_iff (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) {Y : Set β} :
    (ofIso e).rel X Y ↔ V₁.mem Y ∧ phi e hX ⊆ Y := by
  constructor
  · rintro ⟨_, hmem⟩
    have h : (e (V₀.principal hX)).mem Y := hmem
    rw [phi_spec e hX] at h
    exact h
  · intro h
    refine ⟨hX, ?_⟩
    rw [phi_spec e hX]
    exact h

end DomainTheory.NeighbourhoodSystems
