module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.curryFin_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



















/-- **Scott 1976, Theorem 2.3 (The reduction theorem).**
Any continuous function of `k` variables is represented by an element
`u ∈ Pω` via iterated application. -/
theorem theorem_2_3 {n : ℕ} {f : (Fin n → Pomega) → Pomega}
    (hf : IsScottContinuousFin f) :
    ∃ u, ∀ xs, nestApplyFin u xs = f xs :=
  ⟨curryFin f, curryFin_app hf⟩

end DomainTheory.DataTypesAsLattices
