module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.envSet

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Table 2.** Semantics of a LAMBDA term. -/
def interp : Term → (ℕ → Pomega) → Pomega
  | .var i, ρ => ρ i
  | .zero, _ => ofNat 0
  | .succ t, ρ => succSet (interp t ρ)
  | .pred t, ρ => predSet (interp t ρ)
  | .cond z x y, ρ => condSet (interp z ρ) (interp x ρ) (interp y ρ)
  | .app u x, ρ => funOf (interp u ρ) (interp x ρ)
  | .lam i body, ρ => graph (fun v => interp body (envSet ρ i v))

end DomainTheory.DataTypesAsLattices
