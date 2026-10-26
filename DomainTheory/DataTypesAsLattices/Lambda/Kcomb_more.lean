module

public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace Kcomb

theorem beta (x : Pomega) :
    funOf Kcomb x = graph (fun _ => x) :=
  _root_.DomainTheory.DataTypesAsLattices.beta
    (graph_const_isScottContinuous (fun x _ => x)
      (fun _ => id_isScottContinuous)) x

theorem beta2 (x y : Pomega) : funOf (funOf Kcomb x) y = x := by
  rw [Kcomb.beta]
  exact _root_.DomainTheory.DataTypesAsLattices.beta (const_isScottContinuous x) y

end Kcomb

end DomainTheory.DataTypesAsLattices
