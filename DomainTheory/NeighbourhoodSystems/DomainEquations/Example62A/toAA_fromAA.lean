/-ai
Applying toAA after fromAA returns the original element of the separated sum Aⁿ + Aⁿ.

Two elements agree when they contain the same neighbourhoods. If the composite contains the sum master, so does the original element. A left or right product injection in the composite belongs to the original element by the forward half of fromAA_mem_embF or fromAA_mem_embT. Conversely, a neighbourhood of the original element is the master or a product injection of one summand; unpacking that product and applying the reverse characterization shows that it belongs to the composite.
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.AAsys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA_mem_embT

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

theorem toAA_fromAA (hn : 0 < n) (s : (AAsys hn).Element) : toAA hn (fromAA hn s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromAA_mem_embF hn hX).mp hs
    · exact (fromAA_mem_embT hn hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨V, hV, rfl⟩ | ⟨V, hV, rfl⟩
    · exact Or.inl rfl
    · obtain ⟨X, hX, rfl⟩ := hV
      exact Or.inr (Or.inl ⟨X, hX, rfl, (fromAA_mem_embF hn hX).mpr hW⟩)
    · obtain ⟨Y, hY, rfl⟩ := hV
      exact Or.inr (Or.inr ⟨Y, hY, rfl, (fromAA_mem_embT hn hY).mpr hW⟩)

end Example62A

end DomainTheory.NeighbourhoodSystems
