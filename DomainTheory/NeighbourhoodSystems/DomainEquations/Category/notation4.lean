module

public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

export CategoryTheory (Category)

open scoped CategoryTheory

universe u v

scoped notation "𝟙" => CategoryTheory.CategoryStruct.id

end DomainTheory.NeighbourhoodSystems
