/-ai
This file gathers Mathlib's category class together with the notations for the identity morphism and for composition in Scott's after-order, and re-exports the category class. The composite g ⊚ f is f followed by g.
ai-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category.notation4
public import DomainTheory.NeighbourhoodSystems.DomainEquations.compAfter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category.notation6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-!
The category of domains is Mathlib's `CategoryTheory.Category`. Scott writes composition as
"`g` after `f`"; Mathlib writes `f ≫ g` for "`f` then `g`". The notation `g ⊚ f` is that reversed
reading, so `g ⊚ f` is `f ≫ g`.
-/

export CategoryTheory (Category)



end DomainTheory.NeighbourhoodSystems
