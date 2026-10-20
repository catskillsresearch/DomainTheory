/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example78
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Exercise514
import DomainTheory.Neighborhood.Exercise723.Basic
import DomainTheory.Neighborhood.Exercise723.primrec_tri


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

















































/-- `num n m = tri(n+m) + m` is primitive recursive. -/
theorem primrec_num : Nat.Primrec (fun t => num t.unpair.1 t.unpair.2) :=
  (primrec_add₂ (primrec_tri.comp (primrec_add₂ Nat.Primrec.left Nat.Primrec.right))
    Nat.Primrec.right).of_eq fun _ => rfl

end DomainTheory.Neighborhood.Exercise723
