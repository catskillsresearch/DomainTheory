/-ai
Semantic entailment of one formula by another means that every valuation making the first formula true also makes the second formula true.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.formulaSetoid
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.toSet_mk

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- Semantic entailment: `φ ⊨ ψ` iff every valuation satisfying `φ` satisfies `ψ`. -/
def Entails (φ ψ : Formula) : Prop := ∀ v, evalV v φ = true → evalV v ψ = true

end DomainTheory.NeighbourhoodSystems
