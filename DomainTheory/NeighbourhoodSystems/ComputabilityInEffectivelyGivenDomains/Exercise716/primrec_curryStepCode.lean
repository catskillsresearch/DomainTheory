/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise716.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}





theorem primrec_curryStepCode {a e : ℕ → ℕ} (ha : Nat.Primrec a) (he : Nat.Primrec e) :
    Nat.Primrec (fun w => curryStepCode (a w) (e w)) := by
  have h1 : Nat.Primrec (fun w => (e w).unpair.1) := Nat.Primrec.left.comp he
  have h2 : Nat.Primrec (fun w => (e w).unpair.2) := Nat.Primrec.right.comp he
  refine (Nat.Primrec.succ.comp (((ha.pair h1).pair h2).pair (Nat.Primrec.const 0))).of_eq
    (fun w => ?_)
  rfl

end DomainTheory.NeighbourhoodSystems
