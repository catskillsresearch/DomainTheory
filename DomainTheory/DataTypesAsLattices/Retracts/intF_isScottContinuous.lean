/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic


namespace DomainTheory.DataTypesAsLattices













































theorem intF_isScottContinuous : IsScottContinuous intF :=
  graph_const_isScottContinuous
    (fun f u => dcondSet u (ofNat 0) (dcondSet (funOf f (predSet u)) u u))
    (fun u =>
      theorem_1_3
        (f := fun z => dcondSet u (ofNat 0) z)
        (g := fun f => dcondSet (funOf f (predSet u)) u u)
        (dcondSet_isScottContinuous_right u (ofNat 0))
        (theorem_1_3
          (f := fun z => dcondSet z u u)
          (g := fun f => funOf f (predSet u))
          (dcondSet_isScottContinuous_left u u)
          (funOf_isScottContinuous_left (predSet u))))

end DomainTheory.DataTypesAsLattices
