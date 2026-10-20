/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem86
public import DomainTheory.Neighborhood.Theorem88m
public import DomainTheory.Neighborhood.Exercise816.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

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

end DomainTheory.Neighborhood
