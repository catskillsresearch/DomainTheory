/-ai
The sharp injection relates a set X to a set W if and only if X is a neighbourhood of D, W is a sharp neighbourhood, and the zero-embedding of X is contained in W.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.dsharpPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.inSharpMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

@[simp] theorem inSharpMap_rel {X : Set α} {W : Set (List Bool × α)} :
    (inSharpMap hD).rel X W ↔ D.mem X ∧ MemS D W ∧ embZero X ⊆ W := Iff.rfl

end Proposition77

end DomainTheory.NeighbourhoodSystems
