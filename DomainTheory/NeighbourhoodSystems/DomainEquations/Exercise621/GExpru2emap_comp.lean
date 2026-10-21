/-ai
For a strict map g, every expression satisfies T(g ∘ f) = T(g) ∘ T(f). Together with preservation of identities, these are the functor laws of the strict-map category. Strictness of g is required for the coalesced sum and the smash product, whose composition laws use it.

The proof is by induction on T. A constant reduces to the identity law for the identity map of that constant, read in the symmetric direction. The variable is definitional. The separated sum rewrites both components by the inductive hypothesis and applies the composition law of the separated sum. The separated product does the same with the product. The coalesced sum and the smash product do the same, supplying strictness of the two component maps of g by preservation of strictness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusMapTok_comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesMapTok_comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2emap_isStrict

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.prodMapTok_comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.sumMapTok_comp
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **Functor law 2 — `T(g ∘ f) = T(g) ∘ T(f)` for strict `g`.** Together with `map_id`, *these are
all functors* of the strict-map category. The strictness of `g` is needed (and only) for the
coalesced `⊕`/`⊗`, whose composition law `oplusMapTok_comp`/`otimesMapTok_comp` requires it. -/
theorem GExpr.map_comp : (T : GExpr) → {X Y Z : ScottSys} → (f : ApproximableMap X.sys Y.sys) →
    {g : ApproximableMap Y.sys Z.sys} → IsStrict g → T.map (g.comp f) = (T.map g).comp (T.map f)
  | .const D, _, _, _, _, _, _ => (idMap_comp (idMap D.sys)).symm
  | .var, _, _, _, _, _, _ => rfl
  | .sum a b, _, _, _, f, g, hg => by
      show sumMapTok (a.map (g.comp f)) (b.map (g.comp f))
          = (sumMapTok (a.map g) (b.map g)).comp (sumMapTok (a.map f) (b.map f))
      rw [a.map_comp f hg, b.map_comp f hg]
      · exact sumMapTok_comp _ _ _ _
  | .prod a b, _, _, _, f, g, hg => by
      show prodMapTok (a.map (g.comp f)) (b.map (g.comp f))
          = (prodMapTok (a.map g) (b.map g)).comp (prodMapTok (a.map f) (b.map f))
      rw [a.map_comp f hg, b.map_comp f hg]
      · exact prodMapTok_comp _ _ _ _
  | .oplus a b, _, _, _, f, g, hg => by
      show oplusMapTok (a.map (g.comp f)) (b.map (g.comp f))
          = (oplusMapTok (a.map g) (b.map g)).comp (oplusMapTok (a.map f) (b.map f))
      rw [a.map_comp f hg, b.map_comp f hg]
      · exact oplusMapTok_comp _ _ (a.map_isStrict g hg) (b.map_isStrict g hg)
  | .otimes a b, _, _, _, f, g, hg => by
      show otimesMapTok (a.map (g.comp f)) (b.map (g.comp f))
          = (otimesMapTok (a.map g) (b.map g)).comp (otimesMapTok (a.map f) (b.map f))
      rw [a.map_comp f hg, b.map_comp f hg]
      · exact otimesMapTok_comp _ _ (a.map_isStrict g hg) (b.map_isStrict g hg)

end Exercise619
end DomainTheory.NeighbourhoodSystems
