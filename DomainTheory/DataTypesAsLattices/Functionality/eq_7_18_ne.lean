/-ai
Scott 1976, (7.18). For distinct tags j and j', the (m + 1)-fold iterate of the graph of the tagged successor at j, started at the singleton of the pair (j', 0), is bottom.

Induction on m. The zero step unfolds the iterate, applies the tagged successor, and uses the successor rule for a distinct tag. The successor step unfolds the iterate, applies the tagged successor, rewrites by the inductive hypothesis, and uses the bottom rule for the tagged successor.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_app
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_bot
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_succ_ne

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


























/-- **Scott 1976, (7.18).** Distinct tags: `σ_j^{m+1}({(j',0)}) = ⊥`. -/
theorem eq_7_18_ne (j j' m : ℕ) (hne : j ≠ j') :
    Z (m + 1) (graph (sigmaJ j)) {pair j' 0} = botElem := by
  induction m with
  | zero =>
    calc
      Z 1 (graph (sigmaJ j)) {pair j' 0}
        = funOf (graph (sigmaJ j)) {pair j' 0} := rfl
      _ = sigmaJ j {pair j' 0} := sigmaJ_app _ _
      _ = botElem := sigmaJ_succ_ne j j' 0 hne
  | succ m ih =>
    calc
      Z (m + 1 + 1) (graph (sigmaJ j)) {pair j' 0}
        = funOf (graph (sigmaJ j))
            (Z (m + 1) (graph (sigmaJ j)) {pair j' 0}) := rfl
      _ = sigmaJ j (Z (m + 1) (graph (sigmaJ j)) {pair j' 0}) :=
          sigmaJ_app _ _
      _ = sigmaJ j botElem := by rw [ih]
      _ = botElem := sigmaJ_bot j

end DomainTheory.DataTypesAsLattices
