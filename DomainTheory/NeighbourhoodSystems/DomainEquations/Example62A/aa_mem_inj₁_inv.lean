module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Apow
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.apowNe
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.AAsys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

theorem aa_mem_inj₁_inv (hn : 0 < n) {V : Set (Fin n × Str)}
    (h : (AAsys hn).mem (inj₁ V)) : (Apow hn).mem V := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := apowNe hn _ hX'
    exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · rw [inj₁_injective heq]; exact hY'

end Example62A

end DomainTheory.NeighbourhoodSystems
