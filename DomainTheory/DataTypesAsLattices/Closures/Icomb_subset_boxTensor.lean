/-ai
If a and b are closures, the identity combinator is contained in their product.

A pair (n, m) in the identity has m in en. Equation (5.8) recovers en as the square pair of its two projections. Since a and b contain the identity, application is expansive on each projection, and the square pair is monotone, so en lies below the square pair of a and b applied to those projections. That enlarged membership is membership of the pair in the product.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_8
public import DomainTheory.DataTypesAsLattices.Closures.squarePair_mono

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Icomb_subset_boxTensor {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    Icomb ⊆ boxTensor a b := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  have hsub : squarePair (squareFst (e n)) (squareSnd (e n)) ⊆
      squarePair (funOf a (squareFst (e n))) (funOf b (squareSnd (e n))) := by
    refine squarePair_mono ?_ ?_
    · have := funOf_monotone_left ha.1 (squareFst (e n))
      rwa [Icomb_app] at this
    · have := funOf_monotone_left hb.1 (squareSnd (e n))
      rwa [Icomb_app] at this
  refine ⟨n, m, rfl, ?_⟩
  exact hsub (by simpa [eq_5_8] using hm)

end DomainTheory.DataTypesAsLattices
