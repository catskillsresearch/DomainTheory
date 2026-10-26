
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- The recursive content of finite Scott continuity, one argument at a time. -/
def ScottContinuousFin.Body : ∀ {n : ℕ}, ((Fin n → Pomega) → Pomega) → Prop
  | 0, _ => True
  | n + 1, f =>
      (∀ xs : Fin n → Pomega, IsScottContinuous (fun x => f (Fin.cons x xs))) ∧
      (∀ x : Pomega, ScottContinuousFin.Body (fun xs : Fin n → Pomega => f (Fin.cons x xs)))

/-- Continuity of an n-ary map, taken one argument at a time from the left. -/
class ScottContinuousFin {n : ℕ} (f : (Fin n → Pomega) → Pomega) : Prop where
  out : ScottContinuousFin.Body f

end DomainTheory.DataTypesAsLattices
