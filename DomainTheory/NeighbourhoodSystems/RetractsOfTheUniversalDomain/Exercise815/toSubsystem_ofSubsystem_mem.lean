/-ai
The neighbourhood system reconstructed from the filter induced by a subsystem has exactly the neighbourhoods of that subsystem.

In one direction, unwind the two existential witnesses, replace the two generating lists by equality of their finitely generated families, and apply the generator-wise criterion. In the other direction, surjectivity of the presentation supplies an index whose basic neighbourhood is the given neighbourhood, and the singleton list of that index witnesses both filter membership and membership in the finitely generated family.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.principal_mem_finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_le_iff_forall_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.ofSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystemSys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section OrderIso

variable (P : ComputablePresentation D)

/-- **Round trip, membership form.** `toSubsystemSys (ofSubsystem D')` has exactly the same
neighbourhoods as `D'` itself. `→`: unwind the double existential via `nbhdGen_eq_iff` and the
workhorse lemma. `←`: `P.surj` finds an index `n` with `P.X n = Y`; the singleton list `[n]`
witnesses membership on both sides. -/
theorem toSubsystem_ofSubsystem_mem (D' : NeighborhoodSystem α) (hD' : D' ◁ D) (Y : Set α) :
    (toSubsystemSys P (ofSubsystem P D' hD')).mem Y ↔ D'.mem Y := by
  constructor
  · rintro ⟨js, ⟨js', hjseq, hall⟩, hY⟩
    have hfin : finGen P js = finGen P js' := (nbhdGen_eq_iff P).mp hjseq
    exact (finGen_le_iff_forall_mem P hD' js').mpr hall (hfin ▸ hY)
  · intro hY
    obtain ⟨n, hn⟩ := P.surj (hD'.sub hY)
    refine ⟨[n], ⟨[n], rfl, fun i hi => ?_⟩, hn ▸ principal_mem_finGen P (List.mem_singleton.mpr rfl)⟩
    rw [List.mem_singleton] at hi
    subst hi
    rw [hn]
    exact hY

end OrderIso

end DomainTheory.NeighbourhoodSystems
