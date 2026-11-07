module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.existsInitial

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Theorem614

universe w

open CategoryTheory NeighborhoodSystem SmashProduct Theorem614

/-- Scott's Theorem 6.14: existence and uniqueness of homomorphisms into strict algebras. -/
theorem theorem_614 :
    (∀ s : Setup.{w}, ∃ A : TAlgebra s.T,
        Nonempty (Iso (s.T.obj A.carrier) A.carrier) ∧
          ∀ B : TAlgebra s.T, IsStrict B.str → Nonempty (AlgHom A B)) ∧
    (∀ (s : Setup.{w}) (_hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master) (B : TAlgebra s.T) (_hk : IsStrict B.str),
      ∃ g : AlgHom (colimAlg s) B, IsStrict g.hom ∧
        ∀ g' : AlgHom (colimAlg s) B, IsStrict g'.hom → g' = g) :=
  ⟨@exists_algebra_with_hom, @exists_unique_strict_algHom⟩

end DomainTheory.NeighbourhoodSystems.Theorem614
