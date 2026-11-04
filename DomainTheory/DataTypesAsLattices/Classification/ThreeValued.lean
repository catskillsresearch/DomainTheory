module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Closures.botElem
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat_more
public import DomainTheory.DataTypesAsLattices.Classification.uvU
public import DomainTheory.DataTypesAsLattices.Classification.uvV
public import DomainTheory.DataTypesAsLattices.Classification.zeroPrime
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import Mathlib.Data.Set.Finite.Powerset

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

class ThreeValued (x : Pomega) : Prop where
  out : x = botElem ∨ x = ofNat 0 ∨ x = topElem

namespace ThreeValued

theorem uvU_eq_uvV {x y : Pomega} (hx : ThreeValued x) (hy : ThreeValued y) :
    uvU x y = uvV x y ↔ x = ofNat 0 ∨ y = ofNat 0 := by
  rcases hx.out with rfl | rfl | rfl <;> rcases hy.out with rfl | rfl | rfl
  · simp [uvU.bot_bot, uvV.bot_bot, botElem.ne_ofNat_zero]
  · simp [uvU.bot_zero, uvV.bot_zero]
  · constructor
    · intro h
      rw [uvU.bot_top, uvV.bot_top] at h
      exact (zeroPrime.ne_ofNat_zero h.symm).elim
    · intro h
      rcases h with h | h
      · exact (botElem.ne_ofNat_zero h).elim
      · exact (topElem.ne_ofNat_zero h).elim
  · simp [uvU.zero_bot, uvV.zero_bot]
  · simp [uvU.zero_zero, uvV.zero_zero]
  · simp [uvU.zero_top, uvV.zero_top]
  · constructor
    · intro h
      rw [uvU.top_bot, uvV.top_bot] at h
      exact (zeroPrime.ne_ofNat_zero h.symm).elim
    · intro h
      rcases h with h | h
      · exact (topElem.ne_ofNat_zero h).elim
      · exact (botElem.ne_ofNat_zero h).elim
  · simp [uvU.top_zero, uvV.top_zero]
  · constructor
    · intro h
      rw [uvU.top_top, uvV.top_top] at h
      exact (zeroPrime.ne_top h).elim
    · intro h
      rcases h with h | h <;> exact (topElem.ne_ofNat_zero h).elim

end ThreeValued

end DomainTheory.DataTypesAsLattices
