module

public import DomainTheory.DataTypesAsLattices.Enumeration.seq2_right_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.seq2
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.FUN
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Enumeration.graph_mem_FUN

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def Rcomb : Pomega := graph (fun x => seq2 (ofNat 0) x)

namespace Rcomb

theorem app (x : Pomega) : funOf Rcomb x = seq2 (ofNat 0) x :=
  beta (seq2_right_isScottContinuous (ofNat 0)) x

theorem app_zero (x : Pomega) :
    funOf (funOf Rcomb x) (ofNat 0) = ofNat 0 := by
  rw [app, seq2.zero]

theorem mem_FUN : Rcomb ∈ FUN :=
  graph_mem_FUN (seq2_right_isScottContinuous (ofNat 0))

end Rcomb

end DomainTheory.DataTypesAsLattices
