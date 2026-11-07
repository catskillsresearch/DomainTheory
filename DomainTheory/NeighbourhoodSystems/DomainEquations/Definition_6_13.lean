module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.continuousOnDomains

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe w

/-- Scott's Definition 6.13: monotone and continuous functors on subdomains (`MonotoneOnDomains`,
`ContinuousOnDomains`, and `targetFam`). -/
theorem definition_613 (T : Endofunctor DomainObj.{w}) :
    ContinuousOnDomains T ↔
      ∃ hmono : MonotoneOnDomains T,
        ∀ {α : Type w} {E : NeighborhoodSystem α}
          (ℱ : Set (NeighborhoodSystem α)) (hℱ : ∀ ⦃D⦄, D ∈ ℱ → D ◁ E)
          (_hne : ℱ.Nonempty) (_hdir : DirectedOn (· ◁ ·) ℱ)
          {U : NeighborhoodSystem α} (hUE : U ◁ E)
          (_hU : ∀ X, U.mem X ↔ ∃ D ∈ ℱ, D.mem X),
          targetFam T hmono hUE = ⋃ D, ⋃ hD : D ∈ ℱ, targetFam T hmono (hℱ hD) :=
  Iff.rfl

end DomainTheory.NeighbourhoodSystems
