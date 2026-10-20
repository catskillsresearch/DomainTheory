/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition613
public import DomainTheory.Neighborhood.Theorem69
public import DomainTheory.Neighborhood.ApproximableExercises
public import DomainTheory.Neighborhood.Theorem614.Basic
public import DomainTheory.Neighborhood.Theorem614.transport_heq
public import DomainTheory.Neighborhood.Theorem614.isoOfEq_conj
public import DomainTheory.Neighborhood.Theorem614.map_rho_heq

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise510

universe w

namespace Theorem614


variable {α : Type w}













































/-- **`ρₙ₊₁ = i ∘ T(ρₙ) ∘ j`** (Scott's `T(ρₙ) = ρₙ₊₁`, conjugated by the structure iso). Since the
iso `𝒟 ≅ T(𝒟)` is the identity, this is the carrier transport of `T(ρₙ)`; combined with
`map_rho_heq` it pins `ρₙ₊₁`. -/
theorem key_rho (s : Setup.{w}) (n : ℕ) :
    rho s (n + 1) = (colimIso s).hom ⊚ Tmap_rho s n ⊚ (colimIso s).inv := by
  rw [show (colimIso s).hom = (isoOfEq (colimObj_eq s)).hom from rfl,
      show (colimIso s).inv = (isoOfEq (colimObj_eq s)).inv from rfl,
      isoOfEq_conj (colimObj_eq s) (Tmap_rho s n)]
  apply eq_of_heq
  exact HEq.trans (map_rho_heq s n).symm
    (transport_heq (colimObj_eq s) (Tmap_rho s n)).symm

end Theorem614
end DomainTheory.Neighborhood
