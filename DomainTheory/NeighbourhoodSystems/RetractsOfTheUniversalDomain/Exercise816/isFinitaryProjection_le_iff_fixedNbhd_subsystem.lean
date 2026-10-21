/-ai
For finitary projections, one lies below the other exactly when the fixed neighbourhood of the first is a subsystem of the fixed neighbourhood of the second.

A finitary projection is fixed by the operation that sends a map to its finitary part, so the two maps are points of the subtype of maps fixed by that operation. The forward inequality is preserved by the order isomorphism of that subtype with the subsystems. In the reverse direction the subsystem inequality is an inequality of the images, the inverse isomorphism is monotone, and the two round trips restore the original maps.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise816.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Exercise 8.16, Part 1 (Scott 1981, PRG-19).** For finitary projections `a, b : E → E`,
`a ≤ b ↔ D_a ◁ D_b` where `D_a := fixedNbhd a = {X ∈ E ∣ X a X}` (Theorem 8.5's subdomain). This is
exactly Theorem 8.6(a)'s order-isomorphism `finitaryProjectionSubsystemEquiv`, restricted from
`sub`-fixed points to finitary projections via `sub_eq_self_iff_isFinitaryProjection`, and fills the
gap Scott leaves at the end of the proof of Theorem 8.6. -/
theorem isFinitaryProjection_le_iff_fixedNbhd_subsystem {a b : ApproximableMap E E}
    (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
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

end DomainTheory.NeighbourhoodSystems
