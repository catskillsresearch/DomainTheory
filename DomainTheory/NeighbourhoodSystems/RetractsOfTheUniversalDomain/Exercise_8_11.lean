module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DedekindCutProjection

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem example_811 :
    IsProjection DedekindCutProjection.a ∧ Retraction DedekindCutProjection.a ∧ ¬IsFinitary DedekindCutProjection.a :=
  ⟨DedekindCutProjection.isProjection_a, DedekindCutProjection.isRetraction_a, DedekindCutProjection.not_isFinitary_a⟩

