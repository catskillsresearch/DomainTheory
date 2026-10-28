module

public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.omegaComb
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

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

end DomainTheory.DataTypesAsLattices
