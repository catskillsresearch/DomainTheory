/-ai
Every expression preserves strictness: if f is strict, then T(f) is strict.

A constant acts by the identity map, which is strict. The variable is the hypothesis. The separated sum, the coalesced sum, and the smash product are strict for any component maps. The separated product uses the inductive strictness of its two components.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusMapTok_isStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesMapTok_isStrict

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.prodMapTok_isStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.sumMapTok_isStrict
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


/-- **Every `T` preserves strictness.** -/
theorem GExpr.map_isStrict : (T : GExpr) → {X Y : ScottSys} → (f : ApproximableMap X.sys Y.sys) →
    IsStrict f → IsStrict (T.map f)
  | .const _, _, _, _, _ => isStrict_idMap
  | .var, _, _, _, hf => hf
  | .sum a b, _, _, f, _ => sumMapTok_isStrict (a.map f) (b.map f)
  | .prod a b, _, _, f, hf => prodMapTok_isStrict (a.map_isStrict f hf) (b.map_isStrict f hf)
  | .oplus a b, _, _, f, _ => oplusMapTok_isStrict (a.map f) (b.map f)
  | .otimes a b, _, _, f, _ => otimesMapTok_isStrict (a.map f) (b.map f)

end Exercise619
end DomainTheory.NeighbourhoodSystems
