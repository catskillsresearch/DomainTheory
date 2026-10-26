module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.zeroC
public import DomainTheory.DataTypesAsLattices.Lambda.sucC
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.predC
public import DomainTheory.DataTypesAsLattices.Lambda.condC
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices
def ofComb : Comb → (ℕ → Pomega) → Pomega
  | .var i, ρ => ρ i
  | .zero, _ => zeroC
  | .suc, _ => sucC
  | .pred, _ => predC
  | .cond, _ => condC
  | .K, _ => Kcomb
  | .S, _ => Scomb
  | .app u v, ρ => funOf (ofComb u ρ) (ofComb v ρ)

namespace ofComb

theorem update_isScottContinuous (c : Comb) (ρ : ℕ → Pomega) (i : ℕ) :
    IsScottContinuous (fun v => ofComb c (envSet ρ i v)) := by
  induction c generalizing ρ i with
  | var j =>
    constructor
    intro x
    by_cases hj : j = i
    · subst hj; simpa [ofComb, envSet, Function.update] using id_isScottContinuous.out x
    · simpa [ofComb, envSet, Function.update, hj] using (const_isScottContinuous (ρ j)).out x
  | zero => constructor; intro x; simpa [ofComb] using (const_isScottContinuous zeroC).out x
  | suc => constructor; intro x; simpa [ofComb] using (const_isScottContinuous sucC).out x
  | pred => constructor; intro x; simpa [ofComb] using (const_isScottContinuous predC).out x
  | cond => constructor; intro x; simpa [ofComb] using (const_isScottContinuous condC).out x
  | K => constructor; intro x; simpa [ofComb] using (const_isScottContinuous Kcomb).out x
  | S => constructor; intro x; simpa [ofComb] using (const_isScottContinuous Scomb).out x
  | app u v iu iv =>
    exact theorem_1_3.tuple
      (fun y => funOf.isScottContinuous_left y)
      (fun t => funOf.isScottContinuous t)
      (iu ρ i) (iv ρ i)

theorem combinatory (c : Comb) (ρ : ℕ → Pomega)
    (hρ : ∀ i, IsCombinatory (ρ i)) :
    IsCombinatory (ofComb c ρ) := by
  induction c with
  | var i => exact hρ i
  | zero => exact .zero
  | suc => exact .suc
  | pred => exact .pred
  | cond => exact .cond
  | K => exact .K
  | S => exact .S
  | app _ _ iu iv => exact .app iu iv

end ofComb

end DomainTheory.DataTypesAsLattices
