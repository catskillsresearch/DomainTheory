
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.dollarC
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecSubstC
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_more
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecVal

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def secondRecOperator : Pomega :=
  funOf (funOf Scomb (funOf Kcomb dollarC))
    (funOf (funOf Scomb
      (funOf (funOf Scomb (funOf Kcomb Scomb)) Kcomb))
      (funOf Kcomb secondRecSubstC))

namespace secondRecOperator

theorem combinatory : IsCombinatory secondRecOperator :=
  .app (.app .S (.app .K dollarC.combinatory))
    (.app
      (.app .S (.app (.app .S (.app .K .S)) .K))
      (.app .K secondRecSubstC.combinatory))

theorem app (u : Pomega) :
    funOf secondRecOperator u = secondRecVal u := by
  have hsubst :
      (Scomb ⬝ (Scomb ⬝ (Kcomb ⬝ Scomb) ⬝ Kcomb) ⬝ (Kcomb ⬝ secondRecSubstC)) ⬝ u =
        Scomb ⬝ (Kcomb ⬝ u) ⬝ secondRecSubstC := by
    rw [Scomb.beta3, Kcomb.beta2, SK_comp]
  rw [secondRecOperator, SK_comp, hsubst, dollarC.app]
  apply congrArg graph
  funext x
  have hreal (m : ℕ) :
      (Scomb ⬝ (Kcomb ⬝ u) ⬝ secondRecSubstC) ⬝ ofNat m =
        u ⬝ ofNat (secondRecSubst m) := by
    rw [SK_comp, secondRecSubstC.realizes]
  ext k
  simp [seqFun, hreal, secondRecSubst]

end secondRecOperator

end DomainTheory.DataTypesAsLattices
