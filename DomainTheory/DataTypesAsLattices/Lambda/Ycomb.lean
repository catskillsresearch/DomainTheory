module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.omegaComb
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.diagApp_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def Ycomb : Pomega :=
  graph (fun u => funOf (omegaComb u) (omegaComb u))

def Yterm : Term :=
  .lam 0 (.app
    (.lam 1 (.app (.var 0) (.app (.var 1) (.var 1))))
    (.lam 1 (.app (.var 0) (.app (.var 1) (.var 1)))))

namespace Yterm

theorem interp :
    _root_.DomainTheory.DataTypesAsLattices.interp Yterm (fun _ => botElem) =
      Ycomb := by
  simp [Yterm, _root_.DomainTheory.DataTypesAsLattices.interp, Ycomb, omegaComb,
    envSet, Function.update]

end Yterm

namespace Ycomb

theorem app (u : Pomega) :
    funOf Ycomb u = funOf (omegaComb u) (omegaComb u) :=
  beta (theorem_1_3 diagApp_isScottContinuous omegaComb.isScottContinuous) u

theorem combinatory : IsCombinatory Ycomb := by
  simpa [Yterm.interp] using theorem_2_4.closed Yterm

theorem unfold (u : Pomega) :
    funOf Ycomb u = funOf u (funOf Ycomb u) := by
  calc
    funOf Ycomb u = funOf (omegaComb u) (omegaComb u) := Ycomb.app u
    _ = funOf u (funOf (omegaComb u) (omegaComb u)) :=
      omegaComb.app u (omegaComb u)
    _ = funOf u (funOf Ycomb u) := by rw [Ycomb.app]

end Ycomb

end DomainTheory.DataTypesAsLattices
