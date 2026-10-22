module

public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.unnum_numP

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513


variable {α β : Type*}


end DomainTheory.NeighbourhoodSystems.Exercise513

namespace DomainTheory.NeighbourhoodSystems.Exercise513

set_option linter.unusedVariables false

theorem example_513 : ∀ (c : Prod Nat Nat),
  @Eq (Prod Nat Nat)
    (DomainTheory.NeighbourhoodSystems.Exercise513.unnum (DomainTheory.NeighbourhoodSystems.Exercise513.numP c)) c :=
  DomainTheory.NeighbourhoodSystems.Exercise513.unnum_numP

end DomainTheory.NeighbourhoodSystems.Exercise513
