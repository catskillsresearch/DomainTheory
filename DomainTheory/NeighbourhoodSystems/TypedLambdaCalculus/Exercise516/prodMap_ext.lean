/-ai
Two approximable maps from the product of C with itself to C are equal once they agree on every pair of finite shape elements.

Agreement of element maps on principal elements reduces the claim to an arbitrary neighbourhood of the product. That neighbourhood is a product of two neighbourhoods of C, and each is a shape neighbourhood, so it is a product of two shapes. The principal element of that product neighbourhood is the pair of the corresponding shape elements, and the hypothesis applies.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.memC_eq_shape
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.prod_principal_pair

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

















variable {β : Type*}










































/-- Two maps `C × C → C` agree as soon as they agree on every pair of finite elements. -/
theorem prodMap_ext {f g : ApproximableMap (prod C C) C}
    (h : ∀ b₀ σ b₁ τ, f.toElementMap (pair (shapeElem b₀ σ) (shapeElem b₁ τ))
      = g.toElementMap (pair (shapeElem b₀ σ) (shapeElem b₁ τ))) : f = g := by
  apply eq_of_toElementMap_principal
  intro W hW
  obtain ⟨b₀, σ, b₁, τ, rfl⟩ :
      ∃ b₀ σ b₁ τ, W = prodNbhd (shape b₀ σ) (shape b₁ τ) := by
    obtain ⟨X, Y, hX, hY, rfl⟩ := hW
    obtain ⟨b₀, σ, rfl⟩ := memC_eq_shape hX
    obtain ⟨b₁, τ, rfl⟩ := memC_eq_shape hY
    exact ⟨b₀, σ, b₁, τ, rfl⟩
  have heq : (prod C C).principal hW = pair (shapeElem b₀ σ) (shapeElem b₁ τ) :=
    prod_principal_pair b₀ σ b₁ τ
  rw [heq]; exact h b₀ σ b₁ τ

end DomainTheory.NeighbourhoodSystems.Exercise516
