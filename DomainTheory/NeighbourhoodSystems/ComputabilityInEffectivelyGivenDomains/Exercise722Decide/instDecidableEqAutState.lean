module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.autState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instFintypeAutState

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

instance instDecidableEqAutState : (e : SExpr) → DecidableEq (autState e)
  | .sigma => inferInstanceAs (DecidableEq Unit)
  | .single σ => inferInstanceAs (DecidableEq (Option (Fin (σ.length + 1))))
  | .cap a b => by
      letI := instDecidableEqAutState a; letI := instDecidableEqAutState b
      exact inferInstanceAs (DecidableEq (autState a × autState b))
  | .cat a b => by
      letI := instDecidableEqAutState a; letI := instDecidableEqAutState b
      exact inferInstanceAs (DecidableEq (autState a ⊕ autState b))

end Exercise722

end DomainTheory.NeighbourhoodSystems
