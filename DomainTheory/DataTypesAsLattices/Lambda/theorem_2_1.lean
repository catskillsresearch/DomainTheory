/-ai
Scott 1976, Theorem 2.1 (The continuity theorem). For a term t, an environment ρ, and an index i, the interpretation of t is Scott continuous in the value assigned to variable i.

This is the continuity of interpretation in a single variable.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.interp_var_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 2.1 (The continuity theorem).** -/
theorem theorem_2_1 (t : Term) (ρ : ℕ → Pomega) (i : ℕ) :
    IsScottContinuous (fun v => interp t (envSet ρ i v)) :=
  interp_var_isScottContinuous t ρ i

end DomainTheory.DataTypesAsLattices
