/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem74
public import DomainTheory.Neighborhood.Exercise510
public import DomainTheory.Neighborhood.Exercise316
public import DomainTheory.Neighborhood.Exercise715.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}








open Exercise510





section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)



variable {P}















/-- **Exercise 7.15 (Scott 1981, PRG-19) — the infinite iterate `D^∞` is effectively given.** -/
theorem iterSys_isEffectivelyGiven (e : V.IsEffectivelyGiven) :
    (iterSys V).IsEffectivelyGiven := by
  obtain ⟨Q⟩ := e
  exact ⟨iterPresentation (P := Q)⟩

end Iterate
end DomainTheory.Neighborhood
