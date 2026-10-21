/-ai
Scott's account of Plotkin's independent successors states that if z satisfies the eta equation, so that applying z equals applying z to the graph of its own application, and z lies on every endomorphism retract of an endomorphism retract, then one iterate count n serves for every tagged successor test: applying z to the graph of the j-th test and then to the singleton pair of j and 0 yields the singleton pair of j and n.

Plotkin's theorem at the zero test and the singleton pair of 0 and 0 supplies n, and equation (7.18) rewrites the value as that singleton. The case j = 0 is this identity. Otherwise Plotkin's theorem supplies an index for the j-th test, again rewritten by (7.18). A third application, to the union of the two graphs and the union of the two singletons, supplies a common index k, and equation (7.19) rewrites the value as the union of the singleton pairs of 0 with k and of j with k. The monotonicity law for application, using right monotonicity of application of z on each graph inclusion and the inclusion of each singleton in the union, places both computed pairs in that union. Pair injectivity forces the zero-test index to equal k, since the other disjunct would identify j with 0, and it likewise forces the j-th index to equal k. Rewriting then replaces both by n.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_4_plotkin
public import DomainTheory.DataTypesAsLattices.Functionality.eq_7_18_eq
public import DomainTheory.DataTypesAsLattices.Functionality.eq_7_19

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


























/-- Plotkin's independent successors force one common iterate count on all
tagged successor tests. -/
theorem theorem_7_4_sigma_index (z : Pomega)
    (hη : ∀ f, funOf z f = funOf z (graph (fun y => funOf f y)))
    (hz : ∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z) :
    ∃ n, ∀ j,
      funOf (funOf z (graph (sigmaJ j))) {pair j 0} =
        ({pair j n} : Pomega) := by
  obtain ⟨n, hn⟩ :=
    theorem_7_4_plotkin z hη hz (graph (sigmaJ 0)) {pair 0 0}
  refine ⟨n, ?_⟩
  intro j
  have hn' :
      funOf (funOf z (graph (sigmaJ 0))) {pair 0 0} =
        ({pair 0 n} : Pomega) := by
    rw [hn, eq_7_18_eq]
  by_cases hj : j = 0
  · subst j
    exact hn'
  obtain ⟨nj, hnj⟩ :=
    theorem_7_4_plotkin z hη hz (graph (sigmaJ j)) {pair j 0}
  have hnj' :
      funOf (funOf z (graph (sigmaJ j))) {pair j 0} =
        ({pair j nj} : Pomega) := by
    rw [hnj, eq_7_18_eq]
  obtain ⟨k, hk⟩ := theorem_7_4_plotkin z hη hz
    (graph (sigmaJ 0) ∪ graph (sigmaJ j))
    (({pair 0 0} : Pomega) ∪ {pair j 0})
  have hk' :
      funOf
          (funOf z (graph (sigmaJ 0) ∪ graph (sigmaJ j)))
          (({pair 0 0} : Pomega) ∪ {pair j 0}) =
        ({pair 0 k} : Pomega) ∪ {pair j k} := by
    rw [hk, eq_7_19]
  have hmono0 :
      funOf (funOf z (graph (sigmaJ 0))) {pair 0 0} ⊆
        funOf
          (funOf z (graph (sigmaJ 0) ∪ graph (sigmaJ j)))
          (({pair 0 0} : Pomega) ∪ {pair j 0}) :=
    mu_law
      (funOf_monotone_right z Set.subset_union_left)
      Set.subset_union_left
  have hmonoj :
      funOf (funOf z (graph (sigmaJ j))) {pair j 0} ⊆
        funOf
          (funOf z (graph (sigmaJ 0) ∪ graph (sigmaJ j)))
          (({pair 0 0} : Pomega) ∪ {pair j 0}) :=
    mu_law
      (funOf_monotone_right z Set.subset_union_right)
      Set.subset_union_right
  have h0mem : pair 0 n ∈ ({pair 0 k} : Pomega) ∪ {pair j k} := by
    rw [← hk']
    apply hmono0
    rw [hn']
    simp
  have hjmem : pair j nj ∈ ({pair 0 k} : Pomega) ∪ {pair j k} := by
    rw [← hk']
    apply hmonoj
    rw [hnj']
    simp
  have hnk : n = k := by
    rcases h0mem with h0 | h0
    · exact (pair_inj h0).2
    · exact (hj ((pair_inj h0).1).symm).elim
  have hnjk : nj = k := by
    rcases hjmem with hj0 | hjj
    · exact (hj (pair_inj hj0).1).elim
    · exact (pair_inj hjj).2
  rw [hnj', hnjk, ← hnk]

end DomainTheory.DataTypesAsLattices
