/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Exercise510
import DomainTheory.Neighborhood.Exercise316
import DomainTheory.Neighborhood.Exercise715.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}








open Exercise510





section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)



variable {P}















theorem projN_isComputable (P : ComputablePresentation V) (n : ℕ) :
    IsComputableMap (iterPresentation P) P (projN V n) := by
  have hincl : RecDecidable (fun s => P.X s.unpair.1 ⊆ P.X s.unpair.2) := P.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair (nthCode t.unpair.1 n P.masterIdx) t.unpair.2) :=
    ((primrec_nthCode.comp (Nat.Primrec.left.pair
      ((Nat.Primrec.const n).pair (Nat.Primrec.const P.masterIdx)))).of_eq
        (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [iterPresentation_X, projN_rel, fiber_iterEnum, iterIdx, unpair_pair_fst,
    unpair_pair_snd]
  exact ⟨fun h => h.2.2, fun h => ⟨iterEnum_mem _, P.mem_X _, h⟩⟩

end Iterate
end DomainTheory.Neighborhood
