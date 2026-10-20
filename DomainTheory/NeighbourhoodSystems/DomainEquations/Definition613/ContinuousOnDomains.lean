module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613.MonotoneAt
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613.MonotoneOnDomains
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613.targetFam

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe w

/-- **Definition 6.13 (Scott 1981, PRG-19), continuous on domains.** A monotone functor `T` is
*continuous on domains* iff `λD. T(D) : {D ∣ D ◁ E} → {D' ∣ D' ◁ T(E)}` is approximable. In the
neighbourhood framework this is *preservation of directed unions of subsystems*: for any non-empty
directed family `ℱ` of subsystems of `E` whose union is the subsystem `U` (`hU`), the target-side
neighbourhood family of `T(U)` is the union of those of the `T(D)` for `D ∈ ℱ`. -/
def ContinuousOnDomains (T : Endofunctor DomainObj.{w}) : Prop :=
  ∃ hmono : MonotoneOnDomains T,
    ∀ {α : Type w} {E : NeighborhoodSystem α}
      (ℱ : Set (NeighborhoodSystem α)) (hℱ : ∀ ⦃D⦄, D ∈ ℱ → D ◁ E)
      (_hne : ℱ.Nonempty) (_hdir : DirectedOn (· ◁ ·) ℱ)
      {U : NeighborhoodSystem α} (hUE : U ◁ E)
      (_hU : ∀ X, U.mem X ↔ ∃ D ∈ ℱ, D.mem X),
      targetFam T hmono hUE = ⋃ D, ⋃ hD : D ∈ ℱ, targetFam T hmono (hℱ hD)

end DomainTheory.NeighbourhoodSystems
