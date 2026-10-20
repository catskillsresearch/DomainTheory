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
