/-ai
For any subsystem, the finitely generated subsystem of a concatenation is contained in the subsystem if and only if the finitely generated subsystem of each factor is.

Rewrite all three inclusions by the characterization through membership of the generators, and split membership in a concatenation into membership in the two factors.
ai-/
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

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section FinGen

variable (P : ComputablePresentation D)

/-- **The concatenation identity, general form.** For any subsystem `D' ◁ D`,
`Fin(js₁ ++ js₂) ⊆ D'.mem ↔ Fin(js₁) ⊆ D'.mem ∧ Fin(js₂) ⊆ D'.mem` — an immediate corollary of the
workhorse lemma via `List.forall_mem_append`. -/
theorem finGen_append_le_iff {D' : NeighborhoodSystem α} (hD' : D' ◁ D) (js1 js2 : List ℕ) :
    finGen P (js1 ++ js2) ⊆ D'.mem ↔ finGen P js1 ⊆ D'.mem ∧ finGen P js2 ⊆ D'.mem := by
  rw [finGen_le_iff_forall_mem P hD', finGen_le_iff_forall_mem P hD',
    finGen_le_iff_forall_mem P hD', List.forall_mem_append]

end FinGen

end DomainTheory.NeighbourhoodSystems
