/-ai
If an element of the reconstructed system confirms every generator of a finite index list by some witness list, then one witness list confirmed by the element has finitely generated subsystem containing that of the original list.

Proceed by induction on the list. The empty list is witnessed by the empty list, using membership of the master neighbourhood. For a head and a tail, concatenate the witness of the head with the inductive witness of the tail. The element contains the up-set of the concatenation because it contains both up-sets and is closed under intersection. The concatenated system contains the head generator and the tail system by monotonicity along the two sides of the concatenation, using the characterization of inclusion by membership of the generators.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_mono
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.principal_mem_finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGenSys_subsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_le_iff_forall_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section OrderIso

variable (P : ComputablePresentation D)

/-- **The finite-fold lemma.** If every generator `P.X i` (`i ∈ js`) is individually confirmed by
`x` via some witness list, the witnesses can be concatenated (fold over the finite list `js`,
combining via `x.inter_mem`) into a *single* list `js₀` confirmed by `x` with `Fin(js) ⊆
Fin(js₀)`. -/
theorem exists_common_witness (x : (SubD P).Element) {js : List ℕ}
    (h : ∀ i ∈ js, ∃ js', x.mem (nbhdGen P js') ∧ P.X i ∈ finGen P js') :
    ∃ js0, x.mem (nbhdGen P js0) ∧ finGen P js ⊆ finGen P js0 := by
  induction js with
  | nil => exact ⟨[], SubD_master P ▸ x.master_mem, subset_rfl⟩
  | cons j js' ih =>
    obtain ⟨jsj, hxj, hjmem⟩ := h j List.mem_cons_self
    obtain ⟨js0', hx0', hsub0'⟩ := ih (fun i hi => h i (List.mem_cons_of_mem j hi))
    refine ⟨jsj ++ js0', nbhdGen_inter P jsj js0' ▸ x.inter_mem hxj hx0',
      (finGen_le_iff_forall_mem P (finGenSys_subsystem P (jsj ++ js0')) (j :: js')).mpr
        (List.forall_mem_cons.mpr ⟨?_, ?_⟩)⟩
    · exact finGen_mono P (List.sublist_append_left jsj js0') hjmem
    · exact fun i hi =>
        finGen_mono P (List.sublist_append_right jsj js0') (hsub0' (principal_mem_finGen P hi))

end OrderIso

end DomainTheory.NeighbourhoodSystems
