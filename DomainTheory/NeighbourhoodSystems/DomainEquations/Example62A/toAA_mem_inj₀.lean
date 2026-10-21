/-ai
If every component of X belongs to MemA, then toAA z contains the left injection of the proper product of X if and only if z contains the false-tagged tuple of X.

In the forward direction the membership clause is the master, a left injection, or a right injection. The master clause contradicts the basepoint not lying in a left injection. The left clause uses injectivity of the left injection and of proper products. The right clause takes a nonempty witness from apowNe and produces a left-injection token, which cannot lie in a right injection. The reverse direction is the left disjunct.
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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

@[simp] theorem toAA_mem_inj₀ (hn : 0 < n) {z : (Asys n hn).Element} {X : Fin n → Set Str}
    (hX : ∀ j, MemA n (X j)) :
    (toAA hn z).mem (inj₀ (prodN X)) ↔ z.mem (embTuple false X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
    · rw [funext (prodN_injective (inj₀_injective heq))]; exact hz
    · obtain ⟨b, hb⟩ := apowNe hn (prodN X) (apow_mem_prodN hn hX)
      exact absurd (heq ▸ il_mem_inj₀.mpr hb) il_mem_inj₁
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

end Example62A

end DomainTheory.NeighbourhoodSystems
