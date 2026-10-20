module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_9
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_10
public import DomainTheory.DataTypesAsLattices.Closures.boxTensor_app
public import DomainTheory.DataTypesAsLattices.Closures.squarePair_inj

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































/-- **Scott 1976, Theorem 5.4 / analogue of 4.4.** A boxed pair is typed
for `⊠` iff its components are typed. -/
theorem typed_squarePair_boxTensor (a b x y : Pomega) :
    typed (squarePair x y) (boxTensor a b) ↔ typed x a ∧ typed y b := by
  constructor
  · intro h
    have : squarePair x y = squarePair (funOf a x) (funOf b y) := by
      simpa [typed, boxTensor_app, eq_5_9, eq_5_10] using h
    exact squarePair_inj this
  · intro ⟨hx, hy⟩
    rw [typed, boxTensor_app, eq_5_9, eq_5_10, ← hx, ← hy]

end DomainTheory.DataTypesAsLattices
