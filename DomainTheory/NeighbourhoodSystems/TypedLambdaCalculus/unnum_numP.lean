module

public import Mathlib.Logic.Equiv.Nat
import all Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
import all Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
import all Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numP
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.num_injective
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.unnum
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numP_unnum

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise513

theorem unnum_numP (c : ℕ × ℕ) : unnum (numP c) = c :=
  num_injective (by rw [numP_unnum])

end DomainTheory.NeighbourhoodSystems.Exercise513
