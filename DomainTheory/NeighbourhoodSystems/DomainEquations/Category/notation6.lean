module

public import Mathlib.CategoryTheory.Category.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.compAfter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category.notation4

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

export CategoryTheory (Category)

open scoped CategoryTheory

universe u v

scoped infixr:80 " ⊚ " => compAfter

end DomainTheory.NeighbourhoodSystems
