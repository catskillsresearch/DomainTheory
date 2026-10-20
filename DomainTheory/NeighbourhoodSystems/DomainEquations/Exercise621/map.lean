module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplus
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimes
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusMapTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesMapTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.obj

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

/-- **The action of `T` on maps.** -/
def GExpr.map : (T : GExpr) → {X Y : ScottSys} → ApproximableMap X.sys Y.sys →
    ApproximableMap (T.obj X).sys (T.obj Y).sys
  | .const D, _, _, _ => idMap D.sys
  | .var, _, _, f => f
  | .sum a b, _, _, f => sumMapTok (a.map f) (b.map f)
  | .prod a b, _, _, f => prodMapTok (a.map f) (b.map f)
  | .oplus a b, _, _, f => oplusMapTok (a.map f) (b.map f)
  | .otimes a b, _, _, f => otimesMapTok (a.map f) (b.map f)

end Exercise619

end DomainTheory.NeighbourhoodSystems
