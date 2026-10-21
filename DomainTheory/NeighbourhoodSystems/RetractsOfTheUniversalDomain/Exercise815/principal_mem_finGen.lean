/-ai
If an index belongs to a list js, then the basic neighbourhood named by that index belongs to the finitely generated family of js.

The singleton list of the index is a sublist of js, and the basic neighbourhood is a neighbourhood. Extensionality and the membership characterization of the intersection show that the intersection of the master with that singleton equals the basic neighbourhood, because the basic neighbourhood is contained in the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section FinGen

variable (P : ComputablePresentation D)

/-- The single-index generator `P.X i` lies in `Fin(js)` whenever `i ∈ js` (witness: the singleton
sub-selection `[i]`, always `D`-consistent since `interFrom P D.master [i] = D.master ∩ P.X i =
P.X i` using `P.X i ⊆ D.master`). -/
theorem principal_mem_finGen {js : List ℕ} {i : ℕ} (hi : i ∈ js) : P.X i ∈ finGen P js := by
  refine ⟨[i], (List.singleton_sublist).mpr hi, P.mem_X i, ?_⟩
  apply Set.ext
  intro z
  rw [mem_interFrom]
  constructor
  · intro hz
    exact ⟨D.sub_master (P.mem_X i) hz,
      fun j hj => by rw [List.mem_singleton] at hj; subst hj; exact hz⟩
  · rintro ⟨_, hall⟩
    exact hall i (List.mem_singleton.mpr rfl)

end FinGen

end DomainTheory.NeighbourhoodSystems
