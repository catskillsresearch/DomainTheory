/-ai
Scott 1976, (7.18). For a common tag j, the m-fold iterate of the graph of the tagged successor at j, started at the singleton of the pair (j, 0), equals the singleton of the pair (j, m).

Induction on m. The zero step is reflexivity. The successor step unfolds the iterate, applies the tagged successor, rewrites by the inductive hypothesis, and uses the singleton successor rule.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_app
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_succ_singleton

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


























/-- **Scott 1976, (7.18).** Equal tags: `σ_j^m({(j,0)}) = {(j,m)}`. -/
theorem eq_7_18_eq (j m : ℕ) :
    Z m (graph (sigmaJ j)) {pair j 0} = ({pair j m} : Pomega) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    calc
      Z (m + 1) (graph (sigmaJ j)) {pair j 0}
        = funOf (graph (sigmaJ j)) (Z m (graph (sigmaJ j)) {pair j 0}) := rfl
      _ = sigmaJ j (Z m (graph (sigmaJ j)) {pair j 0}) := sigmaJ_app _ _
      _ = sigmaJ j {pair j m} := by rw [ih]
      _ = {pair j (m + 1)} := sigmaJ_succ_singleton j m

end DomainTheory.DataTypesAsLattices
