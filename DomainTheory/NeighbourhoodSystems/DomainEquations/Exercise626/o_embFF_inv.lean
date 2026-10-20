module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok_mem_embF_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftUp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

theorem o_embFF_inv {W : Set Str}
    (h : (D.lift.oplus E.lift).sys.mem (embBit false (embBit false W))) : D.sys.mem W :=
  liftTok_mem_embF_inv (hD := D.ne)
    (oplusTok_mem_embF_inv (D₀ := D.lift.sys) (D₁ := E.lift.sys)
      (h₀ := D.lift.ne) (h₁ := E.lift.ne) h)

end Exercise619

end DomainTheory.NeighbourhoodSystems
