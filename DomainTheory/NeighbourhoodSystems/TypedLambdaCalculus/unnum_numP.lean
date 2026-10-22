module

public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numP
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.num_injective
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.unnum
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numP_unnum

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

theorem unnum_numP (c : ℕ × ℕ) : unnum (numP c) = c :=
  num_injective (by rw [numP_unnum])

end DomainTheory.NeighbourhoodSystems.Exercise513
