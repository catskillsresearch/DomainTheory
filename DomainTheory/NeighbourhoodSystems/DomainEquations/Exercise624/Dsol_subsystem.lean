/-ai
The singleton system on Gamma_D is a subsystem of D summed with the product of D and E.

The master of that sum equals Gamma_D by the master computation and the first fixed-point equation. The only neighbourhood is therefore that master, and the intersection of that neighbourhood with itself is Gamma_D again.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.fTok_GammaD_GammaE
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.master_Fsol

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624


/-- **`{Γ_D} ◁ D + (D × E)`.** The singleton system `D = {Γ_D}` is a subsystem of `D + (D×E)`: by the
fixed point its only neighbourhood `Γ_D` is the master of `D + (D×E)`. -/
theorem Dsol_subsystem : Dsol.sys ◁ (Fsol Dsol Esol).sys := by
  have hmaster : (Fsol Dsol Esol).sys.master = GammaD := master_Fsol.trans fTok_GammaD_GammaE
  refine ⟨hmaster.symm, ?_, ?_⟩
  · intro X hX
    have hXeq : X = GammaD := hX
    rw [hXeq, ← hmaster]
    exact (Fsol Dsol Esol).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = GammaD
    rw [show X = GammaD from hX, show Y = GammaD from hY, Set.inter_self]

end Exercise624
end DomainTheory.NeighbourhoodSystems
