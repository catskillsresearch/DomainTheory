module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descOp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The descent chain `h₀ = ⊥`, `hₙ₊₁ = Op(hₙ)`. -/
def descSeq (k : ApproximableMap (prod V E) E) : ℕ → ApproximableMap (iterSys V) E
  | 0 => constMap (iterSys V) E.bot
  | (n + 1) => descOp k (descSeq k n)

end Target

end Exercise618

end DomainTheory.NeighbourhoodSystems
