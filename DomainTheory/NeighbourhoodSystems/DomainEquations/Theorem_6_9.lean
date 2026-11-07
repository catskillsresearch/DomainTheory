module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.initialHom

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open DomainTheory.NeighbourhoodSystems.SmashProduct

/-- Scott's Theorem 6.9: continuous functors yield a strict algebra homomorphism. -/
theorem theorem_69 :
    ∀ (T : Endofunctor DomainObj), ContinuousOnMaps T →
      ∀ {D : DomainObj} (iso : Iso (T.obj D) D) (B : TAlgebra T),
        IsStrict B.str →
        Nonempty {g : AlgHom (⟨D, iso.hom⟩ : TAlgebra T) B // IsStrict g.hom} :=
  @nonempty_algHom_of_continuousOnMaps

end DomainTheory.NeighbourhoodSystems
