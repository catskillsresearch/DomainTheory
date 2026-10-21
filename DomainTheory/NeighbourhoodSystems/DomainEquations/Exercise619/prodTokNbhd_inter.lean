/-ai
Product neighbourhoods intersect componentwise: the intersection of the product neighbourhoods of X with Y and of X' with Y' is the product neighbourhood of the intersections.

Equality is checked on an arbitrary word. The empty word is handled by simplification of membership in an intersection. A word with a leading bit is handled by cases on that bit, again by simplification of membership in an intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTokNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_false
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_true

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- Scott's (2) for the product: product neighbourhoods intersect componentwise. -/
theorem prodTokNbhd_inter (X X' Y Y' : Set Str) :
    prodTokNbhd X Y ∩ prodTokNbhd X' Y' = prodTokNbhd (X ∩ X') (Y ∩ Y') := by
  ext w
  cases w with
  | nil => simp [Set.mem_inter_iff]
  | cons b w' => cases b <;> simp [Set.mem_inter_iff]

end Exercise619

end DomainTheory.NeighbourhoodSystems
