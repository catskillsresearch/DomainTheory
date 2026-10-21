/-ai
ccEquiv is the order isomorphism from the elements of C to the elements of the three-way sum 𝟙 + C + C, given by toCC with inverse fromCC. The composites are the identity by fromCC_toCC and toCC_fromCC. One element lies below another exactly when its image does, by matching the four shapes of a neighbourhood of C with the master and the three tagged copies, through toCC_mem_j0, toCC_mem_j1, and toCC_mem_j2.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_mem_master3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.memC_cases
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.CC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC_mem_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC_toCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC_fromCC

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

variable {α β γ : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)

variable {V₀ V₁ V₂}

namespace Example62C

/-- **Example 6.2 (Scott 1981, PRG-19) — the isomorphism `|C| ≃o |𝟙 + C + C|`.** -/
def ccEquiv : C.Element ≃o CC.Element where
  toFun := toCC
  invFun := fromCC
  left_inv := fromCC_toCC
  right_inv := toCC_fromCC
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h W hW
      rcases memC_cases (x.sub hW) with rfl | rfl | ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
      · exact x'.master_mem
      · exact toCC_mem_j0.mp (h _ (Or.inr (Or.inl ⟨rfl, hW⟩)))
      · exact (toCC_mem_j1 hA).mp (h _ (Or.inr (Or.inr (Or.inl ⟨A, hA, rfl, hW⟩))))
      · exact (toCC_mem_j2 hA).mp (h _ (Or.inr (Or.inr (Or.inr ⟨A, hA, rfl, hW⟩))))
    · intro h W hW
      rcases hW with rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, h _ hz⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, h _ hz⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, h _ hz⟩))

end Example62C

end DomainTheory.NeighbourhoodSystems
