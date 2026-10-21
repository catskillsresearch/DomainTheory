/-ai
If every entry of a list of natural numbers has a preimage under a function, then the list is the direct image of some list.

Proceed by induction on the list. The empty list is the image of the empty list. For a head and a tail, take a preimage of the head and an inductive preimage of the tail, and place the head's preimage at the front.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

/-- **List-level choice, choice-free.** If every entry of `l` has an `r`-preimage, `l` itself is the
`r`-image of some list — built by ordinary list induction (`Exists.elim` inside a `Prop`-valued goal
at each step), not `Classical.choice`. -/
theorem exists_preimage_of_forall_mem {r : ℕ → ℕ} {l : List ℕ} (h : ∀ i ∈ l, ∃ n, r n = i) :
    ∃ l0 : List ℕ, l0.map r = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons i l' ih =>
    obtain ⟨n0, hn0⟩ := h i List.mem_cons_self
    obtain ⟨l0', hl0'⟩ := ih (fun j hj => h j (List.mem_cons_of_mem i hj))
    exact ⟨n0 :: l0', by simp [hn0, hl0']⟩

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
