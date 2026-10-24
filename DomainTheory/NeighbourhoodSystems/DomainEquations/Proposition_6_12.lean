module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_25
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example_4_4
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_19
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_7
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_21
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_10
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_16
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem_5_6
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Definition_2_1
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_8
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_11
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_12
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_7
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_22
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_29

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
/- concordance: source L3827 PROPOSITION 6.12 projection pair -/
/-- **Proposition 6.12 + Lemma 6.15 packaged.** A subdomain relation `D ◁ E` is in particular a
witness of `D ⊴ E` (take `D' = D`). Together with `trianglelefteq_of_projectionPair`, this shows
`D ⊴ E` holds **iff** there is a projection pair `D ⇄ E`. -/
theorem Subsystem.trianglelefteq {D E : NeighborhoodSystem α} (h : D ◁ E) : D ⊴ E :=
  ⟨D, h, Isomorphic.refl D⟩
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)


end ProjectionPair
end
end DomainTheory.NeighbourhoodSystems
end
