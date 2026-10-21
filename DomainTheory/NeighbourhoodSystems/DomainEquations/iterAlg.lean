/-ai
The infinite iterate of a strict domain, with the cons map as structure map, is a T-algebra for the product endofunctor. The structure map is strict.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.imap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.isStrict_imap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.prodFunctor
public import DomainTheory.NeighbourhoodSystems.DomainEquations.iterObj

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **`𝒟^∞` as a `T`-algebra**, `(𝒟^∞, i)` with `i : 𝒟 × 𝒟^∞ → 𝒟^∞` the "cons" iso (`imap`,
Exercise 3.16's `iterProdIso⁻¹`), strict by `isStrict_imap`. -/
def iterAlg (Dom : StrictDomainObj.{w}) : TAlgebra (prodFunctor Dom) where
  carrier := iterObj Dom
  str := ⟨imap Dom.sys, isStrict_imap⟩

end Exercise618

end DomainTheory.NeighbourhoodSystems
