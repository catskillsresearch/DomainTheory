module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.IsGen
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Dprime
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Basic.notation4

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

@[simp] theorem mem_Dprime {Y : Set β} : (Dprime i j).mem Y ↔ ∃ X, IsGen i j X Y := Iff.rfl

end ProjectionPair

end DomainTheory.NeighbourhoodSystems
