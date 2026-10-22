module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.apowNe
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.AAsys

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

theorem aa_mem_nonempty (hn : 0 < n) {W : Set (Option ((Fin n × Str) ⊕ (Fin n × Str)))}
    (h : (AAsys hn).mem W) : W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨none, none_mem_sumMaster⟩
  · exact inj₀_nonempty (apowNe hn _ hX)
  · exact inj₁_nonempty (apowNe hn _ hY)

end Example62A

end DomainTheory.NeighbourhoodSystems
