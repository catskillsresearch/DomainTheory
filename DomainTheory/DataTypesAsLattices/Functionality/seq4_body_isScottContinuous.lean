/-ai
The nested conditional that defines the four-way sequence, testing the argument and its first three predecessors and returning a, b, c, d, and finally bottom, is Scott continuous.

The continuity theorem for an operation of three arguments is applied once at each conditional. The tests are the identity, the predecessor, the twofold composite of the predecessor, and the threefold composite of the predecessor, each continuous, and the returned values are the constants a, b, c, d, and bottom.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem seq4_body_isScottContinuous (a b c d : Pomega) :
    IsScottContinuous (fun z =>
      condSet z a
        (condSet (predSet z) b
          (condSet (predSet (predSet z)) c
            (condSet (predSet^[3] z) d botElem)))) :=
  continuous_nary
    (fun y t => condSet_isScottContinuous_left y t)
    (fun x t => condSet_isScottContinuous_mid x t)
    (fun x y => condSet_isScottContinuous_right x y)
    id_isScottContinuous (const_isScottContinuous a)
    (continuous_nary
      (fun y t => condSet_isScottContinuous_left y t)
      (fun x t => condSet_isScottContinuous_mid x t)
      (fun x y => condSet_isScottContinuous_right x y)
      predSet_isScottContinuous (const_isScottContinuous b)
      (continuous_nary
        (fun y t => condSet_isScottContinuous_left y t)
        (fun x t => condSet_isScottContinuous_mid x t)
        (fun x y => condSet_isScottContinuous_right x y)
        (theorem_1_3 (f := predSet) (g := predSet)
          predSet_isScottContinuous predSet_isScottContinuous)
        (const_isScottContinuous c)
        (continuous_nary
          (fun y t => condSet_isScottContinuous_left y t)
          (fun x t => condSet_isScottContinuous_mid x t)
          (fun x y => condSet_isScottContinuous_right x y)
          (theorem_1_3 (f := predSet)
            (g := fun z => predSet (predSet z))
            predSet_isScottContinuous
            (theorem_1_3 (f := predSet) (g := predSet)
              predSet_isScottContinuous predSet_isScottContinuous))
          (const_isScottContinuous d) (const_isScottContinuous botElem))))

end DomainTheory.DataTypesAsLattices
