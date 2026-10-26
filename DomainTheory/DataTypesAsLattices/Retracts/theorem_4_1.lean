module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.DirectedSubset
public import DomainTheory.DataTypesAsLattices.Retracts.IsCompactSubset
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.funRetract
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.fstC
public import DomainTheory.DataTypesAsLattices.Retracts.sndC
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.iterateFrom
public import DomainTheory.DataTypesAsLattices.Retracts.lfpAbove
public import DomainTheory.DataTypesAsLattices.Retracts.gfpBelow
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Retracts.vals
public import DomainTheory.DataTypesAsLattices.Retracts.fixpointsCompleteLattice
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Retracts.diagC
public import DomainTheory.DataTypesAsLattices.Retracts.evalC
public import DomainTheory.DataTypesAsLattices.Retracts.curryC
public import DomainTheory.DataTypesAsLattices.Retracts.intF
public import DomainTheory.DataTypesAsLattices.Retracts.treeF
public import DomainTheory.DataTypesAsLattices.Retracts.RetractInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.fixedToInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimitToFixed
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_6_inverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.treeR
public import DomainTheory.DataTypesAsLattices.Retracts.boolR
public import DomainTheory.DataTypesAsLattices.Retracts.openR
public import DomainTheory.DataTypesAsLattices.Retracts.lambF
public import DomainTheory.DataTypesAsLattices.Retracts.lambR
public import DomainTheory.DataTypesAsLattices.Retracts.envR
public import DomainTheory.DataTypesAsLattices.Retracts.updateEnv
public import DomainTheory.DataTypesAsLattices.Retracts.tagInj
public import DomainTheory.DataTypesAsLattices.Retracts.seq4
public import DomainTheory.DataTypesAsLattices.Retracts.tensor4
public import DomainTheory.DataTypesAsLattices.Retracts.plus7Body
public import DomainTheory.DataTypesAsLattices.Retracts.plus7
public import DomainTheory.DataTypesAsLattices.Retracts.expF
public import DomainTheory.DataTypesAsLattices.Retracts.expR
public import DomainTheory.DataTypesAsLattices.Retracts.comp_app
public import DomainTheory.DataTypesAsLattices.Retracts.sUnion_Fixpoints_le_image
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_1_complete
public import DomainTheory.DataTypesAsLattices.Retracts.vals_subset
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.funOf_botElem
public import DomainTheory.DataTypesAsLattices.Retracts.graph_const_bot
public import DomainTheory.DataTypesAsLattices.Retracts.bot_isRetract
public import DomainTheory.DataTypesAsLattices.Retracts.iterates_areRetracts
public import DomainTheory.DataTypesAsLattices.Retracts.bot_retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.iterateBot_isStrict
public import DomainTheory.DataTypesAsLattices.Retracts.iterateBot_retractLe_succ
public import DomainTheory.DataTypesAsLattices.Retracts.iterateBot_retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_mono
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_chain
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_project_later
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_project_earlier
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_project_iUnion
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_iUnion_typed

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.1 (The lattice theorem).**
Fixed points of a continuous function form a complete lattice under `⊆`;
those of a retract form a continuous lattice. -/
theorem theorem_4_1 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (∀ A : Set Pomega, A ⊆ Fixpoints f →
      gfpBelow f (⋂₀ A) ∈ Fixpoints f ∧
        lfpAbove f (⋃₀ A) ∈ Fixpoints f) ∧
      ∀ {a} (_ha : Retract a),
        Fixpoints (funOf a) = {x | typed x a} ∧
          ∀ x : Fixpoints (funOf a),
            DirectedSubset (retractBasis a x) ∧
              (x : Pomega) = ⋃₀ (Subtype.val '' retractBasis a x) := by
  constructor
  · intro A hA
    exact ⟨theorem_4_1_complete f hf A hA, lfpAbove.mem hf hA⟩
  · intro a ha
    constructor
    · ext x
      simp [Fixpoints, typed, eq_comm]
    · intro x
      exact ⟨retractBasis.directedSubset ha x, retractBasis.eq_sUnion ha x⟩

end DomainTheory.DataTypesAsLattices
