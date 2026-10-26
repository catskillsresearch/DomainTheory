
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.squarePair
public import DomainTheory.DataTypesAsLattices.Closures.squareFst
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd
public import DomainTheory.DataTypesAsLattices.Closures.boxTensor
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_8
public import DomainTheory.DataTypesAsLattices.Closures.squarePair_more
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Icomb_subset_boxTensor {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Icomb ⊆ boxTensor a b := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  have hsub : squarePair (squareFst (e n)) (squareSnd (e n)) ⊆
      squarePair (funOf a (squareFst (e n))) (funOf b (squareSnd (e n))) := by
    refine squarePair.mono ?_ ?_
    · have := funOf.monotone_left ha.out.1 (squareFst (e n))
      rwa [Icomb.app] at this
    · have := funOf.monotone_left hb.out.1 (squareSnd (e n))
      rwa [Icomb.app] at this
  refine ⟨n, m, rfl, ?_⟩
  exact hsub (by simpa [eq_5_8] using hm)

end DomainTheory.DataTypesAsLattices
