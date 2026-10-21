/-ai
This file introduces the notation 𝟙 for the identity morphism of a category, and re-exports Mathlib's category class.
ai-/
module

public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

export CategoryTheory (Category)

open scoped CategoryTheory


scoped notation "𝟙" => CategoryTheory.CategoryStruct.id

end DomainTheory.NeighbourhoodSystems
