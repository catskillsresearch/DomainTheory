module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Closures.union_left_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottOpen
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat_more
public import DomainTheory.DataTypesAsLattices.Classification.ThreeValued
public import DomainTheory.DataTypesAsLattices.Classification.charTop
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import Mathlib.Data.Set.Finite.Powerset

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def closedToZero (C : Set Pomega) (x : Pomega) : Pomega :=
  ofNat 0 ∪ charTop Cᶜ x

namespace closedToZero

theorem isScottContinuous (C : Set Pomega) :
    IsScottContinuous (closedToZero C) :=
  theorem_1_3.tuple (f := fun a b => (a ∪ b : Pomega))
    union_left_isScottContinuous
    (fun x => by
      convert union_left_isScottContinuous x using 1
      funext y; exact (Set.union_comm y x).symm)
    (const_isScottContinuous (ofNat 0)) (charTop.isScottContinuous Cᶜ)

theorem threeValued {C : Set Pomega} (hC : IsScottOpen Cᶜ) (x : Pomega) :
    ThreeValued (closedToZero C x) := by
  constructor
  by_cases hx : x ∈ C
  · refine Or.inr (Or.inl ?_)
    have : charTop Cᶜ x = botElem := (charTop.eq_bot_of_closed hC x).mpr hx
    ext k
    simp [closedToZero, this, ofNat, botElem]
  · refine Or.inr (Or.inr ?_)
    have : charTop Cᶜ x = topElem := (charTop.eq_top hC x).mpr hx
    ext k
    simp [closedToZero, this, ofNat, topElem]

theorem eq_zero {C : Set Pomega} (hC : IsScottOpen Cᶜ) (x : Pomega) :
    closedToZero C x = ofNat 0 ↔ x ∈ C := by
  constructor
  · intro h
    by_contra hx
    have htop : charTop Cᶜ x = topElem := (charTop.eq_top hC x).mpr hx
    have : closedToZero C x = topElem := by
      ext k
      simp [closedToZero, htop]
    exact topElem.ne_ofNat_zero (this.symm.trans h)
  · intro hx
    have : charTop Cᶜ x = botElem := (charTop.eq_bot_of_closed hC x).mpr hx
    ext k
    simp [closedToZero, this, ofNat, botElem]

end closedToZero

end DomainTheory.DataTypesAsLattices
