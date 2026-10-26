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
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Retracts.diagC
public import DomainTheory.DataTypesAsLattices.Retracts.evalC
public import DomainTheory.DataTypesAsLattices.Retracts.curryC
public import DomainTheory.DataTypesAsLattices.Retracts.intF
public import DomainTheory.DataTypesAsLattices.Retracts.treeF
public import DomainTheory.DataTypesAsLattices.Retracts.RetractInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.fixedToInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimitToFixed
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


theorem funOf_fix_idem {F : Pomega → Pomega} (hf : IsScottContinuous F)
    (hret : ∀ a, Retract a → Retract (F a)) (x : Pomega) :
    funOf (fix F) (funOf (fix F) x) = funOf (fix F) x := by
  have hchain : ∀ n m, n ≤ m → iterateBot F n ⊆ iterateBot F m :=
    chain_mono (iterateBot F) (iterateBot_mono hf)
  have hidem : ∀ n, funOf (iterateBot F n) (funOf (iterateBot F n) x) =
      funOf (iterateBot F n) x :=
    fun n => retract_app (iterates_areRetracts hret n) x
  have hcl : ∀ n,
      funOf (iterateBot F n) (⋃ m, funOf (iterateBot F m) x) =
        ⋃ m, funOf (iterateBot F n) (funOf (iterateBot F m) x) :=
    fun n => chain_lemma (funOf_isScottContinuous (iterateBot F n))
      (fun m => funOf (iterateBot F m) x)
      (fun m => funOf_monotone_left (iterateBot_mono hf m) x)
  apply subset_antisymm
  · intro k hk
    have hk' : k ∈ funOf (⋃ n, iterateBot F n)
        (⋃ m, funOf (iterateBot F m) x) := by
      simpa [fix, funOf_iUnion] using hk
    obtain ⟨n, hn, hp⟩ := hk'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    have : k ∈ funOf (iterateBot F i) (⋃ m, funOf (iterateBot F m) x) :=
      ⟨n, hn, hi⟩
    have : k ∈ ⋃ m, funOf (iterateBot F i) (funOf (iterateBot F m) x) := by
      rwa [hcl i] at this
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp this
    let N := max i j
    have hij : funOf (iterateBot F i) (funOf (iterateBot F j) x) ⊆
        funOf (iterateBot F N) (funOf (iterateBot F N) x) :=
      mu_law (hchain i N (le_max_left i j))
        (funOf_monotone_left (hchain j N (le_max_right i j)) x)
    have : k ∈ funOf (iterateBot F N) x := by
      have : k ∈ funOf (iterateBot F N) (funOf (iterateBot F N) x) := hij hj
      rwa [hidem N] at this
    simpa [fix, funOf_iUnion] using Set.mem_iUnion.mpr ⟨N, this⟩
  · intro k hk
    have : k ∈ ⋃ n, funOf (iterateBot F n) x := by
      simpa [fix, funOf_iUnion] using hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp this
    have : k ∈ funOf (iterateBot F n) (funOf (iterateBot F n) x) := by
      rw [hidem n]
      exact hkn
    have : k ∈ funOf (iterateBot F n) (⋃ m, funOf (iterateBot F m) x) :=
      funOf_monotone_right _ (Set.subset_iUnion (fun m => funOf (iterateBot F m) x) n) this
    have : k ∈ funOf (⋃ i, iterateBot F i) (⋃ m, funOf (iterateBot F m) x) :=
      funOf_monotone_left (Set.subset_iUnion (iterateBot F) n) _ this
    simpa [fix, funOf_iUnion] using this

end DomainTheory.DataTypesAsLattices
