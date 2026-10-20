module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.kHead

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem kHead_apply (k : ApproximableMap (prod V E) E) (a : V.Element) (u : E.Element) :
    (kHead k a).toElementMap u = k.toElementMap (pair a u) := by
  rw [kHead, toElementMap_comp, toElementMap_paired, toElementMap_constMap, toElementMap_idMap]

end Target

end Exercise618

end DomainTheory.NeighbourhoodSystems
