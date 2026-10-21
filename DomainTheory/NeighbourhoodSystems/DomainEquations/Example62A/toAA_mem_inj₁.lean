/-ai
If every component of Y belongs to MemA, then toAA z contains the right injection of the proper product of Y if and only if z contains the true-tagged tuple of Y.

In the forward direction the membership clause is the master, a left injection, or a right injection. The master clause contradicts the basepoint not lying in a right injection. The left clause takes a nonempty witness from apowNe and produces a left-injection token, which cannot lie in a right injection. The right clause uses injectivity of the right injection and of proper products. The reverse direction is the right disjunct.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.apowNe
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.apow_mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_mem_inj₀

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

@[simp] theorem toAA_mem_inj₁ (hn : 0 < n) {z : (Asys n hn).Element} {Y : Fin n → Set Str}
    (hY : ∀ j, MemA n (Y j)) :
    (toAA hn z).mem (inj₁ (prodN Y)) ↔ z.mem (embTuple true Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
    · obtain ⟨a, ha⟩ := apowNe hn (prodN X') (apow_mem_prodN hn hX')
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
    · rw [funext (prodN_injective (inj₁_injective heq))]; exact hz
  · intro hz; exact Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩)

end Example62A

end DomainTheory.NeighbourhoodSystems
