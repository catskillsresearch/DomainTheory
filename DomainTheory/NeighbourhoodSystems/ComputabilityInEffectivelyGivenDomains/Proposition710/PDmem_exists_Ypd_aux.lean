/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.upSetUnion_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.upSetUnion_cons
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_cons_code

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- The enumeration is onto `ℙ𝒟` (build the index list entry by entry from `P.surj`; choice-free). -/
theorem PDmem_exists_Ypd_aux :
    ∀ (L : List (Set α)), (∀ X ∈ L, V.mem X) → ∃ c, V.Ypd P c = ⋃ X ∈ L, V.upSet X := by
  intro L
  induction L with
  | nil => intro _; exact ⟨0, by rw [V.Ypd_zero P, V.upSetUnion_nil]⟩
  | cons X L ih =>
    intro hL
    obtain ⟨n, hn⟩ := P.surj (hL X (List.mem_cons.mpr (Or.inl rfl)))
    obtain ⟨c', hc'⟩ := ih (fun Y hY => hL Y (List.mem_cons.mpr (Or.inr hY)))
    exact ⟨Nat.pair n c' + 1, by rw [V.Ypd_cons_code P, hn, hc', V.upSetUnion_cons]⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
