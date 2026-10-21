/-ai
Every neighbourhood of the subsystem equals some value of the list-indexed enumeration.

The neighbourhood is the partial meet of a consistent sublist of a finite system belonging to the element. Every index of that sublist has an enumerator preimage, so the sublist is the image of some list. Encoding that list and applying the index-chain specification recovers the neighbourhood, because the partial meet is a neighbourhood of the universal domain.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystemSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q'X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q'X_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.exists_preimage_of_forall_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

/-- **`surj` for `Q'X r`.** Every `D'x`-neighbourhood `Y` is some `Q'X r n`: unwind `Y`'s `finGen`
witness `sub`, use `hspec` + `exists_preimage_of_forall_mem` to find a preimage list `sub0` with
`sub0.map r = sub`, and read off `Y` via the *generic* `Theorem75.idxchain_spec` (applicable because
`sub`'s own consistency — `U.mem (interFrom … sub)` — is exactly `hDY` rewritten along `hYeq`). -/
theorem Q'x_surj (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)
    (hspec : ∀ i, (toSubsystemSys UComputablePresentation x).mem (UX i) ↔ ∃ n, r n = i)
    {Y : Set ℚ} (hY : (toSubsystemSys UComputablePresentation x).mem Y) :
    ∃ n, Q'X r n = Y := by
  obtain ⟨js, hxjs, sub, hsub, hDY, hYeq⟩ := hY
  have hjsmem : ∀ i ∈ js, (toSubsystemSys UComputablePresentation x).mem (UX i) :=
    (mem_nbhdGen_iff UComputablePresentation x js).mp hxjs
  have hsubmem : ∀ i ∈ sub, (toSubsystemSys UComputablePresentation x).mem (UX i) :=
    fun i hi => hjsmem i (hsub.subset hi)
  obtain ⟨sub0, hsub0⟩ := exists_preimage_of_forall_mem (fun i hi => (hspec i).mp (hsubmem i hi))
  refine ⟨encodeList sub0, ?_⟩
  rw [Q'X_eq, decodeList_encodeList, hsub0, hYeq]
  exact idxchain_spec UComputablePresentation (hYeq ▸ hDY)

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
