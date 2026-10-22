module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.IsGen
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Basic.notation4

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- Generators are unique in the first argument (`isGen_mono` both ways). -/
theorem isGen_fst_unique (hji : j.comp i = idMap D) {X X' : Set α} {Y : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X' Y) : X = X' :=
  Set.Subset.antisymm (isGen_mono i j hji h h' subset_rfl)
    (isGen_mono i j hji h' h subset_rfl)

end ProjectionPair

end DomainTheory.NeighbourhoodSystems
