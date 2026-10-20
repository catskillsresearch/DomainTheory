/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise621
import DomainTheory.Neighborhood.Theorem69
import DomainTheory.Neighborhood.Exercise623.Basic
import DomainTheory.Neighborhood.Exercise623.algHom_fix


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB DomainTheory.Neighborhood.Exercise510

namespace Exercise619

















































section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))
















/-- **`descAlgHom` is the least homomorphism**: `val ≤ g` for every homomorphism `g : Exp → D`. The
Kleene iterates `valₙ` lie below any fixed point `g` (induction: `val₀ = ⊥ ≤ g`, and the operator is
monotone with `g` its own fixed point), so their union `val` does too. This is the easy half of
initiality; the matching `g ≤ val` (so `g = val`) is the projection-chain argument of Phase 4. -/
theorem descRel_le_algHom (g : AlgHom (ExpAlg N hN) B) : ∀ n, descRel hN B n ≤ g.hom.1
  | 0 => constBot_le _
  | n + 1 => by
      rw [descRel_succ, algHom_fix hN B g]
      exact comp_mono_gen le_rfl
        (comp_mono_gen ((Texp N).map_mono (descRel_le_algHom g n)) le_rfl)

end Existence
end Exercise619
end DomainTheory.Neighborhood
