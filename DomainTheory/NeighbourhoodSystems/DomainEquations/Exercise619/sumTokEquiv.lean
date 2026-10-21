/-ai
sumTokEquiv is the order isomorphism between elements of the concrete token sum and elements of the abstract separated sum. The forward map is toSum and the inverse is fromSum, and the two round trips are the corresponding identity theorems. The map preserves and reflects order by cases on the three kinds of neighbourhood: the master is shared, and a tagged copy on one side is the matching injection on the other, transported by the membership criteria for the two injections.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_toSum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_fromSum

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- **Exercise 6.19 — the concrete sum is correct up to isomorphism.** The order-isomorphism
`|D₀ + D₁|ₜₒₖ ≃o |D₀ + D₁|` between Scott's `{0,1}*`-presentation and the abstract separated sum. -/
def sumTokEquiv : (sumTok D₀ D₁ h₀ h₁).Element ≃o (sum D₀ D₁ h₀ h₁).Element where
  toFun := toSum
  invFun := fromSum
  left_inv := fromSum_toSum
  right_inv := toSum_fromSum
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hX
      rcases x.sub hX with rfl | ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
      · exact x'.master_mem
      · exact (toSum_mem_inj₀ hA).mp (h _ (Or.inr (Or.inl ⟨A, hA, rfl, hX⟩)))
      · exact (toSum_mem_inj₁ hA).mp (h _ (Or.inr (Or.inr ⟨A, hA, rfl, hX⟩)))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨Y, hY, rfl, h _ hzY⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
