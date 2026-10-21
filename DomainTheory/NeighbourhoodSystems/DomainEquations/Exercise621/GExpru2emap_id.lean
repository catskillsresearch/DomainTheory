/-ai
Every expression preserves identity maps: T of the identity on X is the identity on T(X).

The proof is by induction on T. A constant and the variable are definitional. The separated sum, the separated product, the coalesced sum, and the smash product each rewrite the two components by the inductive hypothesis and apply the identity law of that operation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusMapTok_id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesMapTok_id

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








/-- **Functor law 1 — `T(I_X) = I_{T(X)}`.** -/
theorem GExpr.map_id : (T : GExpr) → (X : ScottSys) → T.map (idMap X.sys) = idMap (T.obj X).sys
  | .const _, _ => rfl
  | .var, _ => rfl
  | .sum a b, X => by
      show sumMapTok (a.map (idMap X.sys)) (b.map (idMap X.sys)) = idMap ((a.obj X).sum (b.obj X)).sys
      rw [a.map_id X, b.map_id X, sumMapTok_id]
  | .prod a b, X => by
      show prodMapTok (a.map (idMap X.sys)) (b.map (idMap X.sys)) = idMap ((a.obj X).prod (b.obj X)).sys
      rw [a.map_id X, b.map_id X, prodMapTok_id]
  | .oplus a b, X => by
      show oplusMapTok (a.map (idMap X.sys)) (b.map (idMap X.sys))
          = idMap ((a.obj X).oplus (b.obj X)).sys
      rw [a.map_id X, b.map_id X, oplusMapTok_id]
  | .otimes a b, X => by
      show otimesMapTok (a.map (idMap X.sys)) (b.map (idMap X.sys))
          = idMap ((a.obj X).otimes (b.obj X)).sys
      rw [a.map_id X, b.map_id X, otimesMapTok_id]

end Exercise619
end DomainTheory.NeighbourhoodSystems
