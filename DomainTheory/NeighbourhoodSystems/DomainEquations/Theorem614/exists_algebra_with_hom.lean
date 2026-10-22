module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.nonempty_algHom

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614


variable {α : Type w}


/-- **Theorem 6.14 (Scott 1981, PRG-19) — the canonical fixed point.** Under the hypotheses
(continuous on maps, monotone and continuous on domains, with a generating set `{Γ} ◁ T({Γ})`), the
iterated colimit `𝒟 = ⋃ₙ Tⁿ({Γ})` is a `T`-algebra whose structure map is an isomorphism
`T(𝒟) ≅ 𝒟` (the identity, since `T(𝒟) = 𝒟`), and there is a homomorphism from `𝒟` into every
`T`-algebra with a strict structure map (Theorem 6.9). This is Scott's *existence* of the initial
`T`-algebra. -/
theorem exists_algebra_with_hom (s : Setup.{w}) :
    ∃ A : TAlgebra s.T, Nonempty (Iso (s.T.obj A.carrier) A.carrier) ∧
      ∀ B : TAlgebra s.T, IsStrict B.str → Nonempty (AlgHom A B) :=
  ⟨colimAlg s, ⟨colimIso s⟩, fun B hk => nonempty_algHom s B hk⟩

end Theorem614
end DomainTheory.NeighbourhoodSystems
