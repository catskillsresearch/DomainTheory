module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.iterProdIso_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.jmap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descOp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The defining action of the operator: `Op(f)(z) = k(z₀, f(⟨z₁,z₂,…⟩))`. -/
theorem descOp_apply (k : ApproximableMap (prod V E) E) (f : ApproximableMap (iterSys V) E)
    (z : (iterSys V).Element) :
    (descOp k f).toElementMap z
      = k.toElementMap (pair (component z 0)
          (f.toElementMap (ofSeq (fun n => component z (n + 1))))) := by
  simp only [descOp, jmap]
  rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, iterProdIso_apply,
    toElementMap_prodMap_pair, toElementMap_idMap]

end Target

end Exercise618

end DomainTheory.NeighbourhoodSystems
