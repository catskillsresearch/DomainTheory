module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_2

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Examples_8_4

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_8

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open Domain.Recursive NeighborhoodSystem
open NeighborhoodSystem ApproximableMap
section
universe u
variable {α : Type u} {E : NeighborhoodSystem α}
/- concordance: source L5163 EXERCISE 8.16 order of projections -/
/-- **Exercise 8.16, Part 1 (Scott 1981, PRG-19).** For finitary projections `a, b : E → E`,
`a ≤ b ↔ D_a ◁ D_b` where `D_a := fixedNbhd a = {X ∈ E ∣ X a X}` (Theorem 8.5's subdomain). This is
exactly Theorem 8.6(a)'s order-isomorphism `finitaryProjectionSubsystemEquiv`, restricted from
`sub`-fixed points to finitary projections via `sub_eq_self_iff_isFinitaryProjection`, and fills the
gap Scott leaves at the end of the proof of Theorem 8.6. -/
theorem isFinitaryProjection_le_iff_fixedNbhd_subsystem {a b : ApproximableMap E E}
    (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    a ≤ b ↔ fixedNbhd a ◁ fixedNbhd b := by
  have hsa : sub a = a := sub_eq_self_iff_isFinitaryProjection.mpr ha
  have hsb : sub b = b := sub_eq_self_iff_isFinitaryProjection.mpr hb
  set fa : {f : ApproximableMap E E // sub f = f} := ⟨a, hsa⟩ with hfa_def
  set fb : {f : ApproximableMap E E // sub f = f} := ⟨b, hsb⟩ with hfb_def
  constructor
  · intro hab
    have hfab : fa ≤ fb := hab
    exact (finitaryProjectionSubsystemEquiv E).monotone hfab
  · intro hD
    have hle : (finitaryProjectionSubsystemEquiv E) fa ≤ (finitaryProjectionSubsystemEquiv E) fb :=
      hD
    have hback := (finitaryProjectionSubsystemEquiv E).symm.monotone hle
    rwa [OrderIso.symm_apply_apply, OrderIso.symm_apply_apply] at hback

/-- **Exercise 8.16 (Scott 1981, PRG-19), in full.**

Part 1: for finitary projections `a, b : E → E`, `a ≤ b ↔ D_a ◁ D_b` (fills the gap at the end of
Theorem 8.6's proof).

Part 2: if `a : E → E` is computable relative to a `ComputablePresentation P` of `E` — i.e. `E` is
effectively given (via `P`) and `a` is computable (relative to `P`) — then `D_a` is effectively
given (finishes off Theorem 8.8's proof). This is `Theorem88m.lean`'s `fixedNbhd_isEffectivelyGiven`,
cited here under the exercise's name. -/
theorem exercise_8_16_assembly :
    (∀ {a b : ApproximableMap E E}, FinitaryProjection a → FinitaryProjection b →
        (a ≤ b ↔ fixedNbhd a ◁ fixedNbhd b)) ∧
      (∀ {P : ComputablePresentation E} {a : ApproximableMap E E},
        ComputableMap P P a → (fixedNbhd a).IsEffectivelyGiven) :=
  ⟨fun ha hb => isFinitaryProjection_le_iff_fixedNbhd_subsystem ha hb,
    fun hcomp => fixedNbhd_isEffectivelyGiven hcomp⟩
end


end DomainTheory.NeighbourhoodSystems

