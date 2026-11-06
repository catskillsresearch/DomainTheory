module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace ApproximableMap

/-- Scott's Exercise 2.9 (forward direction): the elementwise image is the directed union of
images of principal approximations — in membership form,
$Y \in f(x)$ iff $Y \in f(\uparrow X)$ for some $X \in x$. -/
theorem exercise_2_9 :
    ∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (f : ApproximableMap V₀ V₁) (x : V₀.Element) {Y : Set β},
      (f.toElementMap x).mem Y ↔
        ∃ (X : Set α) (hx : x.mem X), (f.toElementMap (V₀.principal (x.sub hx))).mem Y :=
  toElementMap_mem_iff_principal

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
