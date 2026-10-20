module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.AAsys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA_toAA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_fromAA

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

/-- **The isomorphism `|A| ≃o |Aⁿ + Aⁿ|`.** -/
def aaEquiv (hn : 0 < n) : (Asys n hn).Element ≃o (AAsys hn).Element where
  toFun := toAA hn
  invFun := fromAA hn
  left_inv := fromAA_toAA hn
  right_inv := toAA_fromAA hn
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hW
      cases z.sub hW with
      | univ => exact z'.master_mem
      | @tuple i X hX =>
        cases i with
        | false => exact (toAA_mem_inj₀ hn hX).mp (h _ (Or.inr (Or.inl ⟨X, hX, rfl, hW⟩)))
        | true => exact (toAA_mem_inj₁ hn hX).mp (h _ (Or.inr (Or.inr ⟨X, hX, rfl, hW⟩)))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨Y, hY, rfl, h _ hzY⟩)

end Example62A

end DomainTheory.NeighbourhoodSystems
