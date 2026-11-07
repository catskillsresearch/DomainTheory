module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.dsharpRecursion

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Proposition77
section
open NeighborhoodSystem Domain.Recursive ApproximableMap IndefProduct

/-- Scott's Exercise 7.17 (part 1): pairing and second projection on D♯ are computable. -/
theorem example_717 :
    (∀ {α : Type*} {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)
      (P : ComputablePresentation D),
      ComputableMap (prodPresentation (dsharpPresentation P hD) (dsharpPresentation P hD))
        (dsharpPresentation P hD) (pairSharpMap hD)) ∧
    (∀ {α : Type*} {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)
      (P : ComputablePresentation D),
      ComputableMap (dsharpPresentation P hD) (dsharpPresentation P hD) (proj1Map hD)) :=
  ⟨@pairSharp_isComputable, @proj1_isComputable⟩
end


end DomainTheory.NeighbourhoodSystems.Proposition77

namespace DomainTheory.NeighbourhoodSystems.Exercise717
section
open NeighborhoodSystem Domain.Recursive ApproximableMap IndefProduct Proposition77

/-- Scott's Exercise 7.17 (part 2): the g-map is computable. -/
theorem example_717_part2 :
    ∀ {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
      {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}
      (hD : ∀ X, D.mem X → X.Nonempty)
      (P : ComputablePresentation D) (Q : ComputablePresentation E),
      ComputableMap P Q u →
        ComputableMap (prodPresentation Q Q) Q v →
          ComputableMap (dsharpPresentation P hD) Q (gMap u v hD) :=
  @gMap_isComputable
end


end DomainTheory.NeighbourhoodSystems.Exercise717
