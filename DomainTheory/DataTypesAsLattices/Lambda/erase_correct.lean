module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.sucC_app
public import DomainTheory.DataTypesAsLattices.Lambda.predC_app
public import DomainTheory.DataTypesAsLattices.Lambda.condC_beta3
public import DomainTheory.DataTypesAsLattices.Lambda.abs_correct

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


































theorem erase_correct (t : Term) (ρ : ℕ → Pomega) :
    ofComb (erase t) ρ = interp t ρ := by
  induction t generalizing ρ with
  | var i => simp [erase, ofComb, interp]
  | zero => simp [erase, ofComb, interp, zeroC]
  | succ t ih => simp [erase, ofComb, interp, sucC_app, ih]
  | pred t ih => simp [erase, ofComb, interp, predC_app, ih]
  | cond z x y iz ix iy =>
    simp [erase, ofComb, interp, condC_beta3, iz, ix, iy]
  | app u x iu ix => simp [erase, ofComb, interp, iu, ix]
  | lam i body ih =>
    simp only [erase, interp]
    rw [abs_correct]
    congr 1
    funext v
    exact ih (envSet ρ i v)

end DomainTheory.DataTypesAsLattices
