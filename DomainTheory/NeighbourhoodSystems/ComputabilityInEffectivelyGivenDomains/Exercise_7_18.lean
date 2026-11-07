module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.effectiveIso

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap
open DomainTheory.NeighbourhoodSystems.EffectiveIso
/-- Scott's Exercise 7.18: iterate is effectively isomorphic to its iterate. -/
theorem example_718 :
    ∀ {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V),
      EffectivelyIsomorphic (iterPresentation P) (iterPresentation (iterPresentation P)) :=
  @iterSys_effectivelyIsomorphic_iterIter

