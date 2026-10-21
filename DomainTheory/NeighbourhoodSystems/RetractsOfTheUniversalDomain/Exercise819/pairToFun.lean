/-ai
The map from a product into the function space of the truth-value domain sends a pair to the function that returns the first component at true, the second component at false, and the bottom element at bottom. It is the curry of the conditional after the swap that places the truth value in the selection argument.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.swapProdT

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Pairing up, as a function out of `T`.** `pairToFun(x, y) : T → E` sends `t ↦ cond(t, x,
y)`; in particular `true ↦ x`, `false ↦ y`, `⊥ ↦ ⊥` (Exercise 3.26). -/
noncomputable def pairToFun : ApproximableMap (prod E E) (funSpace TD E) :=
  curry ((cond E).comp swapProdT)

end Prod

end DomainTheory.NeighbourhoodSystems
