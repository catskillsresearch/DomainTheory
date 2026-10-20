/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices
































theorem seq4_isScottContinuous_each
    (a b c d : Pomega) :
    (IsScottContinuous fun x => seq4 x b c d) ∧
      (IsScottContinuous fun y => seq4 a y c d) ∧
        (IsScottContinuous fun z => seq4 a b z d) ∧
          IsScottContinuous fun w => seq4 a b c w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact graph_const_isScottContinuous
      (fun x z => condSet z x
        (condSet (predSet z) b
          (condSet (predSet (predSet z)) c
            (condSet (predSet^[3] z) d botElem))))
      (fun z => condSet_isScottContinuous_mid z _)
  · exact graph_const_isScottContinuous
      (fun y z => condSet z a
        (condSet (predSet z) y
          (condSet (predSet (predSet z)) c
            (condSet (predSet^[3] z) d botElem))))
      (fun z => theorem_1_3 (condSet_isScottContinuous_right z a)
        (condSet_isScottContinuous_mid (predSet z) _))
  · exact graph_const_isScottContinuous
      (fun z' t => condSet t a
        (condSet (predSet t) b
          (condSet (predSet (predSet t)) z'
            (condSet (predSet^[3] t) d botElem))))
      (fun t => theorem_1_3 (condSet_isScottContinuous_right t a)
        (theorem_1_3 (condSet_isScottContinuous_right (predSet t) b)
          (condSet_isScottContinuous_mid (predSet (predSet t)) _)))
  · exact graph_const_isScottContinuous
      (fun w t => condSet t a
        (condSet (predSet t) b
          (condSet (predSet (predSet t)) c
            (condSet (predSet^[3] t) w botElem))))
      (fun t => theorem_1_3 (condSet_isScottContinuous_right t a)
        (theorem_1_3 (condSet_isScottContinuous_right (predSet t) b)
          (theorem_1_3 (condSet_isScottContinuous_right (predSet (predSet t)) c)
            (condSet_isScottContinuous_mid (predSet^[3] t) botElem))))

end DomainTheory.DataTypesAsLattices
