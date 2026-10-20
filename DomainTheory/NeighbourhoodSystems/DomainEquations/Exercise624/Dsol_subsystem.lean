/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise619PartB
public import DomainTheory.Neighborhood.Exercise624.Basic
public import DomainTheory.Neighborhood.Exercise624.fTok_GammaD_GammaE
public import DomainTheory.Neighborhood.Exercise624.master_Fsol

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB

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
end DomainTheory.Neighborhood
