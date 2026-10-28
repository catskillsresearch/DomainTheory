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

theorem exercise_8_16_assembly :
    (∀ {a b : ApproximableMap E E}, FinitaryProjection a → FinitaryProjection b →
        (a ≤ b ↔ fixedNbhd a ◁ fixedNbhd b)) ∧
      (∀ {P : ComputablePresentation E} {a : ApproximableMap E E},
        ComputableMap P P a → (fixedNbhd a).IsEffectivelyGiven) :=
  ⟨fun ha hb => isFinitaryProjection_le_iff_fixedNbhd_subsystem ha hb,
    fun hcomp => fixedNbhd_isEffectivelyGiven hcomp⟩
end

end DomainTheory.NeighbourhoodSystems
