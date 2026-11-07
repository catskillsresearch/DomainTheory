module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.initialAlgebra

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- Scott's Definition 6.5: an initial `T`-algebra admits a unique homomorphism into
every other `T`-algebra. -/
theorem definition_65 {Obj : Type u} [Category Obj] {T : Endofunctor Obj} {A : TAlgebra T}
    (hA : IsInitial A) (B : TAlgebra T) :
    ∃ h : AlgHom A B, ∀ h' : AlgHom A B, h' = h :=
  ⟨hA.desc B, hA.uniq B⟩

end DomainTheory.NeighbourhoodSystems
