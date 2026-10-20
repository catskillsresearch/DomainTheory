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













































theorem intF_map_isScottContinuous (f : Pomega) :
    IsScottContinuous (fun u =>
      dcondSet u (ofNat 0) (dcondSet (funOf f (predSet u)) u u)) :=
  theorem_1_3_nary
    (fun y z => dcondSet_isScottContinuous_left y z)
    (fun x z => dcondSet_isScottContinuous_mid x z)
    (fun x y => dcondSet_isScottContinuous_right x y)
    id_isScottContinuous
    (const_isScottContinuous (ofNat 0))
    (theorem_1_3_nary
      (fun y z => dcondSet_isScottContinuous_left y z)
      (fun x z => dcondSet_isScottContinuous_mid x z)
      (fun x y => dcondSet_isScottContinuous_right x y)
      (theorem_1_3 (funOf_isScottContinuous f) predSet_isScottContinuous)
      id_isScottContinuous
      id_isScottContinuous)

end DomainTheory.DataTypesAsLattices
