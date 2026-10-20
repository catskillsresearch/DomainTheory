/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.GRel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- `embZero X ≠ embPair P Q` from `P ∈ 𝒟^§` (no `D.mem X` needed). -/
theorem embZero_ne_embPair_of_memS (hD : ∀ X, D.mem X → X.Nonempty)
    {X : Set α} {P Q : Set (List Bool × α)} (hP : MemS D P) :
    embZero X ≠ embPair P Q := by
  intro h
  obtain ⟨z, hz⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Q)
  have hz0 : z ∈ embZero X := h ▸ hz
  have hpath : z.1 = [] := hz0.1
  rcases hz with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
  · rw [hp'] at hpath; simp at hpath
  · rw [hq'] at hpath; simp at hpath

end Exercise717

end DomainTheory.NeighbourhoodSystems
