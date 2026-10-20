/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.sucC_app
import DomainTheory.DataTypesAsLattices.Lambda.succSet_ofNat


namespace DomainTheory.DataTypesAsLattices






















































theorem ofNat_combinatory : ∀ n, IsCombinatory (ofNat n)
  | 0 => by
    simpa [zeroC] using IsCombinatory.zero
  | n + 1 => by
    have h := IsCombinatory.app IsCombinatory.suc (ofNat_combinatory n)
    simpa [sucC_app, succSet_ofNat] using h

end DomainTheory.DataTypesAsLattices
