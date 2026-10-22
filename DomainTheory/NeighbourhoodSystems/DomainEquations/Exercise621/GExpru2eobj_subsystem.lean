module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusTok_subsystem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesTok_subsystem

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.sumTok_subsystem
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


/-- **`λX. T(X)` is monotone on domains.** -/
theorem GExpr.obj_subsystem : (T : GExpr) → {X Y : ScottSys} → X.sys ◁ Y.sys →
    (T.obj X).sys ◁ (T.obj Y).sys
  | .const D, _, _, _ => Subsystem.refl D.sys
  | .var, _, _, h => h
  | .sum a b, _, _, h => sumTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)
  | .prod a b, _, _, h => prodTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)
  | .oplus a b, _, _, h => oplusTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)
  | .otimes a b, _, _, h => otimesTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)

end Exercise619
end DomainTheory.NeighbourhoodSystems
