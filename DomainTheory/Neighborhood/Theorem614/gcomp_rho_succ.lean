/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition613
import DomainTheory.Neighborhood.Theorem69
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Theorem614.Basic
import DomainTheory.Neighborhood.Theorem614.key_rho


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise510

universe w

namespace Theorem614


variable {α : Type w}















































/-- **The fixed-point recursion `gₙ₊₁ = k ∘ T(gₙ) ∘ j`.** Using `key_rho` (`ρₙ₊₁ = i∘T(ρₙ)∘j`) and the
homomorphism square `g ∘ i = k ∘ T(g)`. -/
theorem gcomp_rho_succ (s : Setup.{w}) (B : TAlgebra s.T) (g : AlgHom (colimAlg s) B) (n : ℕ) :
    g.hom.comp (rho s (n + 1))
      = B.str.comp ((s.T.map (X := objColim s) (Y := B.carrier)
          (g.hom.comp (rho s n))).comp (colimIso s).inv) := by
  have hcomm : g.hom ⊚ (colimIso s).hom
      = B.str ⊚ s.T.map (X := objColim s) (Y := B.carrier) g.hom := g.comm
  show g.hom ⊚ rho s (n + 1)
      = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) (g.hom ⊚ rho s n)) ⊚ (colimIso s).inv
  calc g.hom ⊚ rho s (n + 1)
      = g.hom ⊚ ((colimIso s).hom ⊚ (Tmap_rho s n ⊚ (colimIso s).inv)) :=
          congrArg (fun x => g.hom ⊚ x) (key_rho s n)
    _ = (g.hom ⊚ (colimIso s).hom) ⊚ (Tmap_rho s n ⊚ (colimIso s).inv) :=
          (Category.assoc g.hom (colimIso s).hom (Tmap_rho s n ⊚ (colimIso s).inv)).symm
    _ = (B.str ⊚ s.T.map (X := objColim s) (Y := B.carrier) g.hom)
            ⊚ (Tmap_rho s n ⊚ (colimIso s).inv) := by rw [hcomm]
    _ = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) g.hom
            ⊚ (Tmap_rho s n ⊚ (colimIso s).inv)) :=
          Category.assoc B.str (s.T.map (X := objColim s) (Y := B.carrier) g.hom)
            (Tmap_rho s n ⊚ (colimIso s).inv)
    _ = B.str ⊚ ((s.T.map (X := objColim s) (Y := B.carrier) g.hom ⊚ Tmap_rho s n)
            ⊚ (colimIso s).inv) :=
          congrArg (B.str ⊚ ·)
            (Category.assoc (s.T.map (X := objColim s) (Y := B.carrier) g.hom) (Tmap_rho s n)
              (colimIso s).inv).symm
    _ = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) (g.hom ⊚ rho s n)
            ⊚ (colimIso s).inv) :=
          congrArg (fun m => B.str ⊚ (m ⊚ (colimIso s).inv))
            (s.T.map_comp (X := objColim s) (Y := objColim s) (Z := B.carrier) g.hom
              (rho s n)).symm

end Theorem614
end DomainTheory.Neighborhood
