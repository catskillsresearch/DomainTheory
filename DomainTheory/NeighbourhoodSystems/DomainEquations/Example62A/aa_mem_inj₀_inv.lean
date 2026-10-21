/-ai
If the left injection of a set V is a neighbourhood of the separated sum Aⁿ + Aⁿ, then V is a neighbourhood of the n-fold power of A.

The membership splits into the sum master, a left summand, or a right summand. The master case is impossible because the basepoint belongs to the master and not to a left injection. The left case uses injectivity of the left injection. The right case takes a nonempty witness from apowNe and produces a right-injection token, which cannot lie in a left injection.
ai-/
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

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

theorem aa_mem_inj₀_inv (hn : 0 < n) {V : Set (Fin n × Str)}
    (h : (AAsys hn).mem (inj₀ V)) : (Apow hn).mem V := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
  · rw [inj₀_injective heq]; exact hX'
  · obtain ⟨b, hb⟩ := apowNe hn _ hY'
    exact absurd (heq ▸ ir_mem_inj₁.mpr hb) ir_mem_inj₀

end Example62A

end DomainTheory.NeighbourhoodSystems
