module

public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.abs
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.ofComb
public import DomainTheory.DataTypesAsLattices.Lambda.sucC
public import DomainTheory.DataTypesAsLattices.Lambda.predC
public import DomainTheory.DataTypesAsLattices.Lambda.condC
public import DomainTheory.DataTypesAsLattices.Lambda.zeroC
public import DomainTheory.DataTypesAsLattices.Lambda.condC_more
public import DomainTheory.DataTypesAsLattices.Lambda.predC_more
public import DomainTheory.DataTypesAsLattices.Lambda.sucC_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def erase : Term → Comb
  | .var i => .var i
  | .zero => .zero
  | .succ t => .app .suc (erase t)
  | .pred t => .app .pred (erase t)
  | .cond z x y => .app (.app (.app .cond (erase x)) (erase y)) (erase z)
  | .app u x => .app (erase u) (erase x)
  | .lam i body => abs i (erase body)

namespace erase

theorem correct (t : Term) (ρ : ℕ → Pomega) :
    ofComb (erase t) ρ = interp t ρ := by
  induction t generalizing ρ with
  | var i => simp [erase, ofComb, interp]
  | zero => simp [erase, ofComb, interp, zeroC]
  | succ t ih => simp [erase, ofComb, interp, sucC.app, ih]
  | pred t ih => simp [erase, ofComb, interp, predC.app, ih]
  | cond z x y iz ix iy =>
    simp [erase, ofComb, interp, condC.beta3, iz, ix, iy]
  | app u x iu ix => simp [erase, ofComb, interp, iu, ix]
  | lam i body ih =>
    simp only [erase, interp]
    rw [abs.correct]
    congr 1
    funext v
    exact ih (envSet ρ i v)

end erase

end DomainTheory.DataTypesAsLattices
