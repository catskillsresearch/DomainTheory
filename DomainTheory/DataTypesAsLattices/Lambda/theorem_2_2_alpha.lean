module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Table 1 (α).** Bound variables may be renamed when the
bodies agree after the rename (Scott: "`x` is a bound variable"). -/
theorem theorem_2_2_alpha (i j : ℕ) (body : Term) (ρ : ℕ → Pomega)
    (h : ∀ v, interp body (envSet ρ i v) =
            interp (rename i j body) (envSet ρ j v)) :
    interp (.lam i body) ρ = interp (.lam j (rename i j body)) ρ := by
  unfold interp
  exact congrArg graph (funext h)

end DomainTheory.DataTypesAsLattices
