module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem memS_embPair_inv {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)
    {P Q : Set (List Bool × α)} (h : MemS D (embPair P Q)) : MemS D P ∧ MemS D Q := by
  generalize hW : embPair P Q = W at h
  cases h with
  | gamma =>
    exfalso
    obtain ⟨a, ha⟩ := hD D.master D.master_mem
    have h1 : (([], a) : List Bool × α) ∈ Gamma D := ha
    rw [← hW] at h1
    rcases h1 with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
    · simp at hp'
    · simp at hq'
  | @zero X hX =>
    exfalso
    obtain ⟨t, ht⟩ := embZero_nonempty (hD X hX)
    have hempty : t.1 = [] := ht.1
    rw [← hW] at ht
    rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
    · rw [hp'] at hempty; simp at hempty
    · rw [hq'] at hempty; simp at hempty
  | @pair P' Q' hP' hQ' =>
    obtain ⟨hPP, hQQ⟩ := embPair_injective hW
    rw [hPP, hQQ]; exact ⟨hP', hQ'⟩

end Example61

end DomainTheory.NeighbourhoodSystems
