
module

public import DomainTheory.DataTypesAsLattices.Retracts.updateEnv
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem updateEnv_isScottContinuous_t (x : Pomega) (n : ℕ) :
    IsScottContinuous (fun t => updateEnv t x n) :=
  graph_const_isScottContinuous
    (fun t m => if m = ofNat n then x else funOf t m)
    (fun m => by
      by_cases h : m = ofNat n
      · simpa [h] using const_isScottContinuous (c := x)
      · simpa [h] using funOf.isScottContinuous_left m)

end DomainTheory.DataTypesAsLattices
