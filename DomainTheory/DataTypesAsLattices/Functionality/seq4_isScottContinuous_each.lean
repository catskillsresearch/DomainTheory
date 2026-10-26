
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem
public import DomainTheory.DataTypesAsLattices.Functionality.mem
public import DomainTheory.DataTypesAsLattices.Functionality.emptyE
public import DomainTheory.DataTypesAsLattices.Functionality.singletonE
public import DomainTheory.DataTypesAsLattices.Functionality.arrowE
public import DomainTheory.DataTypesAsLattices.Functionality.prodE
public import DomainTheory.DataTypesAsLattices.Functionality.sumE
public import DomainTheory.DataTypesAsLattices.Functionality.Ea
public import DomainTheory.DataTypesAsLattices.Functionality.kerE
public import DomainTheory.DataTypesAsLattices.Functionality.Nrel
public import DomainTheory.DataTypesAsLattices.Functionality.Nk
public import DomainTheory.DataTypesAsLattices.Functionality.sumMed
public import DomainTheory.DataTypesAsLattices.Functionality.inleftC
public import DomainTheory.DataTypesAsLattices.Functionality.inrightC
public import DomainTheory.DataTypesAsLattices.Functionality.outleftC
public import DomainTheory.DataTypesAsLattices.Functionality.outrightC
public import DomainTheory.DataTypesAsLattices.Functionality.whichC
public import DomainTheory.DataTypesAsLattices.Functionality.outC
public import DomainTheory.DataTypesAsLattices.Functionality.pairMed
public import DomainTheory.DataTypesAsLattices.Functionality.Z
public import DomainTheory.DataTypesAsLattices.Functionality.Zcomb
public import DomainTheory.DataTypesAsLattices.Functionality.iterateE
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ
public import DomainTheory.DataTypesAsLattices.Functionality.eraseTag
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinRel
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinGood
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinE
public import DomainTheory.DataTypesAsLattices.Functionality.Hinterp
public import DomainTheory.DataTypesAsLattices.Functionality.encodeExp
public import DomainTheory.DataTypesAsLattices.Functionality.Htyped
public import DomainTheory.DataTypesAsLattices.Functionality.expTag
public import DomainTheory.DataTypesAsLattices.Functionality.expPayload
public import DomainTheory.DataTypesAsLattices.Functionality.hApply
public import DomainTheory.DataTypesAsLattices.Functionality.updateEnvUnion
public import DomainTheory.DataTypesAsLattices.Functionality.hVar
public import DomainTheory.DataTypesAsLattices.Functionality.hZero
public import DomainTheory.DataTypesAsLattices.Functionality.hSucc
public import DomainTheory.DataTypesAsLattices.Functionality.hPred
public import DomainTheory.DataTypesAsLattices.Functionality.hCond
public import DomainTheory.DataTypesAsLattices.Functionality.hApp
public import DomainTheory.DataTypesAsLattices.Functionality.hLam
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep
public import DomainTheory.DataTypesAsLattices.Functionality.HF
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun
public import DomainTheory.DataTypesAsLattices.Functionality.Hcomb
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem_tag_ne

@[expose] public section


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
      (fun z => condSet.isScottContinuous_mid z _)
  · exact graph_const_isScottContinuous
      (fun y z => condSet z a
        (condSet (predSet z) y
          (condSet (predSet (predSet z)) c
            (condSet (predSet^[3] z) d botElem))))
      (fun z => theorem_1_3 (condSet.isScottContinuous_right z a)
        (condSet.isScottContinuous_mid (predSet z) _))
  · exact graph_const_isScottContinuous
      (fun z' t => condSet t a
        (condSet (predSet t) b
          (condSet (predSet (predSet t)) z'
            (condSet (predSet^[3] t) d botElem))))
      (fun t => theorem_1_3 (condSet.isScottContinuous_right t a)
        (theorem_1_3 (condSet.isScottContinuous_right (predSet t) b)
          (condSet.isScottContinuous_mid (predSet (predSet t)) _)))
  · exact graph_const_isScottContinuous
      (fun w t => condSet t a
        (condSet (predSet t) b
          (condSet (predSet (predSet t)) c
            (condSet (predSet^[3] t) w botElem))))
      (fun t => theorem_1_3 (condSet.isScottContinuous_right t a)
        (theorem_1_3 (condSet.isScottContinuous_right (predSet t) b)
          (theorem_1_3 (condSet.isScottContinuous_right (predSet (predSet t)) c)
            (condSet.isScottContinuous_mid (predSet^[3] t) botElem))))

end DomainTheory.DataTypesAsLattices
