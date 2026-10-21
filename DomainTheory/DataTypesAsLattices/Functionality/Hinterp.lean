/-ai
Scott 1976, (4.42) and (4.43). The interpretation of a lambda term is a map from environments to lambda values. A variable looks up its index in the environment. Zero is the left injection of the numeral zero. Successor and predecessor test the which-projection of the subterm and, on the integer side, inject the successor or predecessor of the out-projection, otherwise returning the bottom element. A conditional tests the which-projection of the test and then its out-projection, chooses among the three branches, and retracts the result into the lambda retract. An application returns the bottom element on the integer side and otherwise applies the out-projection of the operator to the argument. An abstraction is the right injection of the graph of the body in the environment updated at the bound index.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.inleftC
public import DomainTheory.DataTypesAsLattices.Functionality.inrightC
public import DomainTheory.DataTypesAsLattices.Functionality.whichC
public import DomainTheory.DataTypesAsLattices.Functionality.outC

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.42)–(4.43).** Semantics `ℋ⟦τ⟧ : env → lamb`. -/
def Hinterp : LambTerm → Pomega → Pomega
  | .var n, t => funOf t (ofNat n)
  | .zero, _ => funOf inleftC (ofNat 0)
  | .succ τ, t =>
      condSet (funOf whichC (Hinterp τ t))
        (funOf inleftC (succSet (funOf outC (Hinterp τ t))))
        botElem
  | .pred τ, t =>
      condSet (funOf whichC (Hinterp τ t))
        (funOf inleftC (predSet (funOf outC (Hinterp τ t))))
        botElem
  | .condq θ τ σ ρ, t =>
      funOf lambR (condSet (funOf whichC (Hinterp θ t))
        (condSet (funOf outC (Hinterp θ t)) (Hinterp τ t) (Hinterp σ t))
        (Hinterp ρ t))
  | .app τ σ, t =>
      condSet (funOf whichC (Hinterp τ t)) botElem
        (funOf (funOf outC (Hinterp τ t)) (Hinterp σ t))
  | .lam n τ, t =>
      funOf inrightC (graph (fun x => Hinterp τ (updateEnv t x n)))

end DomainTheory.DataTypesAsLattices
