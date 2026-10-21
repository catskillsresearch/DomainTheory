/-ai
For every lambda term and every environment, the combinatory interpretation of the erasure equals the interpretation of the term.

The proof is by induction on the term. Variables, zero, successor, predecessor, conditionals, and applications reduce by the definitions of erasure, combinatory interpretation, and interpretation, using the application laws for successor, predecessor, and the three-place conditional. An abstraction rewrites by the correctness of abstraction, and the inductive hypothesis applies in the environment updated at the bound index.
ai-/
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
