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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.UPX
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.mem_UPX

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

theorem UPX_cons (b : ℕ) (l : List ℕ) :
    V.UPX P (b :: l) = V.upSet (P.X b) ∪ V.UPX P l := by
  ext z
  rw [Set.mem_union, V.mem_UPX P, V.mem_UPX P]
  constructor
  · rintro ⟨c, hc, hz⟩
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact Or.inl hz
    · exact Or.inr ⟨c, hc', hz⟩
  · rintro (hz | ⟨c, hc, hz⟩)
    · exact ⟨b, List.mem_cons.mpr (Or.inl rfl), hz⟩
    · exact ⟨c, List.mem_cons.mpr (Or.inr hc), hz⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
