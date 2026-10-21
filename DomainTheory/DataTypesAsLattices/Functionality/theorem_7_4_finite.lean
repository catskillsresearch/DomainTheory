/-ai
If z is extensional in its function argument and lies in every iterator functionality, and if for every j the application of z to the graph of σ_j sends the singleton of the code of (j, 0) to the singleton of the code of (j, n), then the double application of z to the finite sets e_p and e_q equals the n-fold iterate of e_p at e_q.

Let j be one more than the maximum of p and q, let one graph be the graph of application of e_p, and let the other be its union with the graph of σ_j. These graphs are related by the Plotkin equivalence, so functionality relates their images under z, and the pair of e_q with e_q union the singleton of (j, 0) is related, hence so are the two double applications. Plotkin's lemma writes each as some iterate. The graph law for the iterator makes the left value the pure iterate of e_p at e_q, and finite separation writes the right value as an iterate union the singleton of (j, m). Erasing the tag j, by the two erasure lemmas, identifies the pure iterates. Monotonicity of application places the tagged value of the pure σ_j branch inside the right-hand value, so the tag n equals m, either because a tag inside the pure iterate is excluded or because injectivity of pairing reads the singleton. Extensionality then replaces e_p by its graph, and the iterates agree at n.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Z_graph_funOf
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_4_plotkin
public import DomainTheory.DataTypesAsLattices.Functionality.Z_finite_no_tag
public import DomainTheory.DataTypesAsLattices.Functionality.plotkin_finite_separation
public import DomainTheory.DataTypesAsLattices.Functionality.eraseTag_Z_finite
public import DomainTheory.DataTypesAsLattices.Functionality.eraseTag_Z_finite_union
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinE_erase
public import DomainTheory.DataTypesAsLattices.Functionality.plotkin_function_related

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






























theorem theorem_7_4_finite (z : Pomega)
    (hη : ∀ f, funOf z f = funOf z (graph (fun y => funOf f y)))
    (hz : ∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z)
    {n : ℕ}
    (hn : ∀ j, funOf (funOf z (graph (sigmaJ j))) {pair j 0} =
      ({pair j n} : Pomega))
    (p q : ℕ) :
    funOf (funOf z (e p)) (e q) = Z n (e p) (e q) := by
  let j := max p q + 1
  let gf := graph (fun y => funOf (e p) y)
  let gu := gf ∪ graph (sigmaJ j)
  have hfg : (arrowE
      (plotkinE p q j) (plotkinE p q j)).rel gf gu := by
    simpa [j, gf, gu] using plotkin_function_related p q
  have hzfg :
      (arrowE (plotkinE p q j) (plotkinE p q j)).rel
        (funOf z gf) (funOf z gu) :=
    (hz (plotkinE p q j)).2.2 gf gu hfg
  have hstart :
      (plotkinE p q j).rel (e q) (e q ∪ {pair j 0}) := by
    refine ⟨⟨0, Or.inl rfl⟩, ⟨0, Or.inr rfl⟩, ?_⟩
    exact Relation.EqvGen.rel _ _
      ⟨0, Or.inl ⟨rfl, rfl⟩⟩
  have hout :
      (plotkinE p q j).rel
        (funOf (funOf z gf) (e q))
        (funOf (funOf z gu) (e q ∪ {pair j 0})) :=
    hzfg.2.2 _ _ hstart
  obtain ⟨r, hr⟩ := theorem_7_4_plotkin z hη hz gf (e q)
  obtain ⟨m, hm⟩ :=
    theorem_7_4_plotkin z hη hz gu (e q ∪ {pair j 0})
  have hleft :
      funOf (funOf z gf) (e q) = Z r (e p) (e q) := by
    rw [hr]
    exact Z_graph_funOf r (e p) (e q)
  have hright :
      funOf (funOf z gu) (e q ∪ {pair j 0}) =
        Z m (e p) (e q) ∪ {pair j m} := by
    rw [hm]
    simpa [j, gf, gu] using plotkin_finite_separation p q m
  have herase := plotkinE_erase hout
  have horbit : Z r (e p) (e q) = Z m (e p) (e q) := by
    rw [hleft, hright] at herase
    exact (eraseTag_Z_finite p q r).symm.trans
      (herase.trans (eraseTag_Z_finite_union p q m))
  have hsigmaSub :
      funOf (funOf z (graph (sigmaJ j))) {pair j 0} ⊆
        funOf (funOf z gu) (e q ∪ {pair j 0}) := by
    exact mu_law
      (funOf_monotone_right z Set.subset_union_right)
      Set.subset_union_right
  have htag : pair j n ∈ Z m (e p) (e q) ∪ {pair j m} := by
    rw [← hright]
    apply hsigmaSub
    rw [hn j]
    simp
  have hnm : n = m := by
    rcases htag with hbad | htag
    · exact (Z_finite_no_tag p q m n (by simpa [j] using hbad)).elim
    · exact (pair_inj htag).2
  rw [hη (e p), hleft, horbit, ← hnm]

end DomainTheory.DataTypesAsLattices
