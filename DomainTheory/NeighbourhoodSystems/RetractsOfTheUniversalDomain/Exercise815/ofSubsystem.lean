/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_le_iff_forall_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.self_mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section OrderIso

variable (P : ComputablePresentation D)

/-- **Forward direction: a subsystem induces a filter of `SubD`.** Given `D' ◁ D`, the filter
`ofSubsystem P D' hD'` consists of the neighbourhoods `nbhd(js)` such that `D'` already contains
every singleton generator `P.X i` for `i ∈ js`. -/
def ofSubsystem (D' : NeighborhoodSystem α) (hD' : D' ◁ D) : (SubD P).Element where
  mem N := ∃ js, N = nbhdGen P js ∧ ∀ i ∈ js, D'.mem (P.X i)
  sub := fun ⟨js, hN, _⟩ => ⟨js, hN⟩
  master_mem := ⟨[], rfl, fun i hi => absurd hi List.not_mem_nil⟩
  inter_mem := by
    rintro N1 N2 ⟨js1, rfl, h1⟩ ⟨js2, rfl, h2⟩
    exact ⟨js1 ++ js2, nbhdGen_inter P js1 js2, List.forall_mem_append.mpr ⟨h1, h2⟩⟩
  up_mem := by
    rintro N1 N2 ⟨js1, rfl, h1⟩ ⟨js2, rfl⟩ hsub
    have hle : finGen P js2 ⊆ finGen P js1 := hsub (self_mem_nbhdGen P js1)
    exact ⟨js2, rfl, (finGen_le_iff_forall_mem P hD' js2).mp
      (hle.trans ((finGen_le_iff_forall_mem P hD' js1).mpr h1))⟩

end OrderIso

end DomainTheory.NeighbourhoodSystems
