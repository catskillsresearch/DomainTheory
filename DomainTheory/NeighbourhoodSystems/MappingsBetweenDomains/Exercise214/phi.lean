module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 2.14 — the correspondence `φ`.** For a domain isomorphism `e` and `X ∈ 𝒟₀`, `φ(X)` is
the neighbourhood with `e(↑X) = ↑φ(X)` provided by Theorem 2.7. -/
noncomputable def phi (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) : Set β :=
  Classical.choose (exists_principal_eq_apply_principal e hX)

end DomainTheory.NeighbourhoodSystems
