module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.squarePair
public import DomainTheory.DataTypesAsLattices.Closures.squareFst
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd
public import DomainTheory.DataTypesAsLattices.Closures.boxTensor
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_9
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_10
@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 5.4 / analogue of 4.4.** Projections of a
`⊠`-typed point remain typed. -/
theorem typed_of_boxTensor {a b u : Pomega} (hu : typed u (boxTensor a b)) :
    typed (squareFst u) a ∧ typed (squareSnd u) b := by
  have : u = squarePair (funOf a (squareFst u)) (funOf b (squareSnd u)) := by
    simpa [typed, boxTensor.app] using hu
  exact ⟨congrArg squareFst this |>.trans (eq_5_9 _ _),
    congrArg squareSnd this |>.trans (eq_5_10 _ _)⟩

end DomainTheory.DataTypesAsLattices
