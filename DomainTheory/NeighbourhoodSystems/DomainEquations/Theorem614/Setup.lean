module


public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises

@[expose] public section

universe w

namespace DomainTheory.NeighbourhoodSystems
namespace Theorem614

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {α : Type w}

/-- The hypotheses of Theorem 6.14, bundled: a functor `T` that is continuous on maps, monotone and
continuous on domains, together with a generating system `Γ` over a token type `Tok` such that
`{Γ} ◁ T({Γ})` (the carrier of `T({Γ})` is identified with `Tok` by `ceq`, and `hsub` is Scott's
`{Γ} ◁ T({Γ})`). -/
structure Setup where
  /-- The functor. -/
  T : Endofunctor DomainObj.{w}
  /-- `T` is continuous on maps (Definition 6.8). -/
  hmaps : ContinuousOnMaps T
  /-- `T` is monotone on domains (Definition 6.13). -/
  hmono : MonotoneOnDomains T
  /-- `T` is continuous on domains (Definition 6.13). -/
  hcont : ContinuousOnDomains T
  {Tok : Type w}
  /-- The generating system `{Γ}`. -/
  Γ : NeighborhoodSystem Tok
  /-- `T({Γ})` is a system over the same token type. -/
  ceq : (T.obj ⟨Tok, Γ⟩).carrier = Tok
  /-- Scott's hypothesis `{Γ} ◁ T({Γ})`. -/
  hsub : Γ ◁ (ceq ▸ (T.obj ⟨Tok, Γ⟩).sys : NeighborhoodSystem Tok)

end Theorem614
end DomainTheory.NeighbourhoodSystems
