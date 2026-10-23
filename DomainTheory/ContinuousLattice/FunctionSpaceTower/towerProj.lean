module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceProjection
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap

@[expose] public section

namespace DomainTheory.ContinuousLattice

attribute [instance] CLat.str

/-- The projection tower from Scott's recursion immediately before Theorem 4.4:
`j_{n+1} = [j_n → j_n]`, anchored at `j₀ : [D₀ → D₀] → D₀`.

At each successor, the maps and projection laws are the diagonal specialization
`proposition_3_7_projection P P`.  `conjMap` supplies the outer Scott-continuity needed to bundle
those canonical maps as an `IsContinuousLatticeProjection`. -/
noncomputable def towerProj (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier)) :
    ∀ n, IsContinuousLatticeProjection (towerType D₀ n) (towerType D₀ (n + 1))
  | 0 => j₀
  | (n + 1) => functionSpaceProjection (towerProj D₀ j₀ n)

namespace towerProj

theorem succ (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier)) (n : ℕ) :
    let P := towerProj D₀ j₀ n
    (towerProj D₀ j₀ (n + 1)).incl = conjMap P.incl P.retr ∧
      (towerProj D₀ j₀ (n + 1)).retr = conjMap P.retr P.incl := by
  exact ⟨rfl, rfl⟩

section Tower

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- **Scott 1972, recursion before Theorem 4.4 (from Proposition 3.7).**
`i_{n+1}(x) = iₙ ∘ x ∘ jₙ`. -/
theorem succ_incl_apply (n : ℕ) (x : towerType D₀ (n + 1)) (y : towerType D₀ (n + 1)) :
    ((towerProj D₀ j₀ (n + 1)).incl x) y
      = (towerProj D₀ j₀ n).incl (x ((towerProj D₀ j₀ n).retr y)) := rfl

/-- **Scott 1972, recursion before Theorem 4.4 (from Proposition 3.7).**
`j_{n+1}(x') = jₙ ∘ x' ∘ iₙ`. -/
theorem succ_retr_apply (n : ℕ) (x' : towerType D₀ (n + 2)) (y : towerType D₀ n) :
    ((towerProj D₀ j₀ (n + 1)).retr x') y
      = (towerProj D₀ j₀ n).retr (x' ((towerProj D₀ j₀ n).incl y)) := rfl

/-- **Scott 1972, §4 (application is preserved).** `iₙ(f(x)) = i_{n+1}(f)(iₙ(x))` for `f ∈ D_{n+1}`,
`x ∈ Dₙ`. The embeddings turn functional application into application one level up. -/
theorem incl_apply (n : ℕ) (f : towerType D₀ (n + 1)) (x : towerType D₀ n) :
    (towerProj D₀ j₀ n).incl (f x)
      = ((towerProj D₀ j₀ (n + 1)).incl f) ((towerProj D₀ j₀ n).incl x) := by
  rw [succ_incl_apply, (towerProj D₀ j₀ n).retr_incl]

end Tower

end towerProj

end DomainTheory.ContinuousLattice
