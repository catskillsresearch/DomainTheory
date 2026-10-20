/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise619PartB
import DomainTheory.Neighborhood.Exercise624.Basic
import DomainTheory.Neighborhood.Exercise624.gTok_GammaD_GammaE
import DomainTheory.Neighborhood.Exercise624.master_Gsol


namespace DomainTheory.Neighborhood

open NeighborhoodSystem DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB

namespace Exercise624

















/-- **`{Γ_E} ◁ D + E`.** The singleton system `E = {Γ_E}` is a subsystem of `D + E`: by the fixed
point its only neighbourhood `Γ_E` is the master of `D + E`. -/
theorem Esol_subsystem : Esol.sys ◁ (Gsol Dsol Esol).sys := by
  have hmaster : (Gsol Dsol Esol).sys.master = GammaE := master_Gsol.trans gTok_GammaD_GammaE
  refine ⟨hmaster.symm, ?_, ?_⟩
  · intro X hX
    have hXeq : X = GammaE := hX
    rw [hXeq, ← hmaster]
    exact (Gsol Dsol Esol).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = GammaE
    rw [show X = GammaE from hX, show Y = GammaE from hY, Set.inter_self]

end Exercise624
end DomainTheory.Neighborhood
