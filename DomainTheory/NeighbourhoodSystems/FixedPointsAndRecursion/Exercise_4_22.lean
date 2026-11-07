module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.peanoSub

@[expose] public section

open DomainTheory.NeighbourhoodSystems


theorem example_422 :
    ∀ {M : Type*} (zero : M) (succ : M → M),
      (∀ n, zero ≠ succ n) → Function.Injective succ →
        Nonempty (PeanoModel (Nat' zero succ)) :=
  @exists_peano_submodel

