/-ai
This file introduces the infix notation ⊚ for composition in Scott's after-order, so that g ⊚ f means f followed by g, and re-exports Mathlib's category class.
ai-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.compAfter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category.notation4

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

export CategoryTheory (Category)

open scoped CategoryTheory


scoped infixr:80 " ⊚ " => compAfter

end DomainTheory.NeighbourhoodSystems
