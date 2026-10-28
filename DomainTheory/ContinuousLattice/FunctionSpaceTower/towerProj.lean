module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceProjection
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap

@[expose] public section

namespace DomainTheory.ContinuousLattice

attribute [instance] CLat.str

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

theorem succ_incl_apply (n : ℕ) (x : towerType D₀ (n + 1)) (y : towerType D₀ (n + 1)) :
    ((towerProj D₀ j₀ (n + 1)).incl x) y
      = (towerProj D₀ j₀ n).incl (x ((towerProj D₀ j₀ n).retr y)) := rfl

theorem succ_retr_apply (n : ℕ) (x' : towerType D₀ (n + 2)) (y : towerType D₀ n) :
    ((towerProj D₀ j₀ (n + 1)).retr x') y
      = (towerProj D₀ j₀ n).retr (x' ((towerProj D₀ j₀ n).incl y)) := rfl

theorem incl_apply (n : ℕ) (f : towerType D₀ (n + 1)) (x : towerType D₀ n) :
    (towerProj D₀ j₀ n).incl (f x)
      = ((towerProj D₀ j₀ (n + 1)).incl f) ((towerProj D₀ j₀ n).incl x) := by
  rw [succ_incl_apply, (towerProj D₀ j₀ n).retr_incl]

end Tower

end towerProj

end DomainTheory.ContinuousLattice
