/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.galois
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.inj_bounded

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair








/-- **Exercise 6.25 — `g` preserves `⊔` (not just *directed* unions).** For any bounded set `S`,
`g(⊔S) = ⊔ {g(s) ∣ s ∈ S}`. This is the characteristic property of a lower adjoint.

* `⊒`: `g(⊔S)` is an upper bound of `{g(s)}` since `s ⊑ ⊔S` and `g` is monotone.
* `⊑`: by the Galois connection it suffices that `⊔S ⊑ h(⊔{g(s)})`, i.e. that each `s ⊑ h(⊔{g(s)})`;
  by the Galois connection again this is `g(s) ⊑ ⊔{g(s)}`, true by `le_sSup`. -/
theorem inj_sSup (P : ProjectionPair D E) {S : Set D.Element} (hS : D.Bounded S) :
    P.inj.toElementMap (D.sSup S hS) =
      E.sSup (P.inj.toElementMap '' S) (P.inj_bounded hS) := by
  apply le_antisymm
  · refine (P.galois _ _).mpr (D.sSup_le S hS fun s hs => ?_)
    refine (P.galois s _).mp ?_
    exact E.le_sSup _ (P.inj_bounded hS) ⟨s, hs, rfl⟩
  · refine E.sSup_le _ (P.inj_bounded hS) ?_
    rintro _ ⟨s, hs, rfl⟩
    exact P.inj.toElementMap_mono (D.le_sSup S hS hs)

end Subsystem.ProjectionPair
end DomainTheory.NeighbourhoodSystems
