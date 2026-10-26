module

public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.comp_app
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_ofNat_zero
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_ofNat_one
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_of_zero_not_pos
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_of_pos_not_zero
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_of_mixed
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_of_empty
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_cases
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
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
public import DomainTheory.DataTypesAsLattices.Functionality.inleftC
public import DomainTheory.DataTypesAsLattices.Functionality.inrightC
public import DomainTheory.DataTypesAsLattices.Functionality.outleftC
public import DomainTheory.DataTypesAsLattices.Functionality.outrightC
public import DomainTheory.DataTypesAsLattices.Functionality.whichC
public import DomainTheory.DataTypesAsLattices.Functionality.outC
public import DomainTheory.DataTypesAsLattices.Functionality.pairMed
public import DomainTheory.DataTypesAsLattices.Functionality.iterateE
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
public import DomainTheory.DataTypesAsLattices.Functionality.hPred
public import DomainTheory.DataTypesAsLattices.Functionality.hCond
public import DomainTheory.DataTypesAsLattices.Functionality.hApp
public import DomainTheory.DataTypesAsLattices.Functionality.HF
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun
public import DomainTheory.DataTypesAsLattices.Functionality.Hcomb
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app_bot
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app_top

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.13).** `(a ⊕ b) ∘ (a' ⊕ b') = (a ∘ a') ⊕ (b ∘ b')`. -/
theorem eq_4_13 (a b a' b' : Pomega) :
    comp (plusR a b) (plusR a' b') = plusR (comp a a') (comp b b') := by
  apply graph_ext
  intro u
  rw [plusR_app a' b' u]
  rcases dcondSet.cases (funOf u (ofNat 0)) with h | h | h | h
  · rw [dcondSet.of_zero_not_pos h.1 h.2, plusR_app,
      pairSeq_app_zero, pairSeq_app_one, dcondSet.ofNat_zero,
      dcondSet.of_zero_not_pos h.1 h.2]
    simp only [comp_app]
  · rw [dcondSet.of_pos_not_zero h.1 h.2, plusR_app,
      pairSeq_app_zero, pairSeq_app_one, dcondSet.ofNat_one,
      dcondSet.of_pos_not_zero h.1 h.2]
    simp only [comp_app]
  · rw [dcondSet.of_mixed h.1 h.2, plusR_app_top, dcondSet.of_mixed h.1 h.2]
  · rw [dcondSet.of_empty h.1 h.2, plusR_app_bot, dcondSet.of_empty h.1 h.2]

end DomainTheory.DataTypesAsLattices
