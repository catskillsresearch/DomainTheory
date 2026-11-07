module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.computableMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap

/-- Scott's Definition 7.2: a map is computable when its neighbourhood relation is
recursively enumerable, and an element is computable when the neighbourhoods it
meets are recursively enumerable. -/
theorem definition_72 {α β : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ComputablePresentation V) (Q : ComputablePresentation W)
    (f : ApproximableMap V W) (y : W.Element) :
    (ComputableMap P Q f ↔ REPred₂ (fun n m => f.rel (P.X n) (Q.X m))) ∧
      (ComputableElement Q y ↔ REPred (fun m => y.mem (Q.X m))) :=
  ⟨⟨fun h => h.out, fun h => ⟨h⟩⟩, ⟨fun h => h.out, fun h => ⟨h⟩⟩⟩

end DomainTheory.NeighbourhoodSystems
