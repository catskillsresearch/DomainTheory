/-ai
For finitary projections on a neighbourhood system, one lies below the other exactly when the fixed neighbourhood of the first is a subsystem of the fixed neighbourhood of the second. If a map is computable relative to a computable presentation, then its fixed neighbourhood is effectively given.

The comparison is the finitary case of the order isomorphism between projections and subsystems. Effective givenness is the corresponding clause of Theorem 8.8.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise816.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise816.isFinitaryProjection_le_iff_fixedNbhd_subsystem

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.ComputablePresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72.ComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88m.fixedNbhd_isEffectivelyGiven
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Exercise 8.16 (Scott 1981, PRG-19), in full.**

Part 1: for finitary projections `a, b : E → E`, `a ≤ b ↔ D_a ◁ D_b` (fills the gap at the end of
Theorem 8.6's proof).

Part 2: if `a : E → E` is computable relative to a `ComputablePresentation P` of `E` — i.e. `E` is
effectively given (via `P`) and `a` is computable (relative to `P`) — then `D_a` is effectively
given (finishes off Theorem 8.8's proof). This is `Theorem88m.lean`'s `fixedNbhd_isEffectivelyGiven`,
cited here under the exercise's name. -/
theorem exercise_8_16 :
    (∀ {a b : ApproximableMap E E}, FinitaryProjection a → FinitaryProjection b →
        (a ≤ b ↔ fixedNbhd a ◁ fixedNbhd b)) ∧
      (∀ {P : ComputablePresentation E} {a : ApproximableMap E E},
        ComputableMap P P a → (fixedNbhd a).IsEffectivelyGiven) :=
  ⟨fun ha hb => isFinitaryProjection_le_iff_fixedNbhd_subsystem ha hb,
    fun hcomp => fixedNbhd_isEffectivelyGiven hcomp⟩

end DomainTheory.NeighbourhoodSystems
