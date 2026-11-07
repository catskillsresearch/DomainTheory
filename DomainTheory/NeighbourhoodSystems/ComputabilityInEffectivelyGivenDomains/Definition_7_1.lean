module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.rePred
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.computablePresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive

/-- Scott's Definition 7.1: a computable presentation enumerates the neighbourhoods
so that intersection and consistency are recursively decidable, and therefore so
are inclusion and equality of neighbourhoods. -/
theorem definition_71 {α : Type*} (V : NeighborhoodSystem α) :
    (V.IsEffectivelyGiven ↔ Nonempty (ComputablePresentation V)) ∧
      (∀ P : ComputablePresentation V, RecDecidable₂ (fun n m => P.X n ⊆ P.X m)) ∧
        (∀ P : ComputablePresentation V, RecDecidable₂ (fun n m => P.X n = P.X m)) :=
  ⟨Iff.rfl, fun P => P.incl_computable, fun P => P.eq_computable⟩

end DomainTheory.NeighbourhoodSystems
