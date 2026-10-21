/-ai
One formula entails another if and only if the evaluation set of the first is contained in the evaluation set of the second.

If entailment holds and a natural number lies in the first evaluation set, the bit bridge makes the first formula true under the bits of that number, entailment makes the second formula true, and the bridge returns membership in the second evaluation set. Conversely, if the evaluation sets are nested and a valuation makes the first formula true, some natural number agrees with that valuation on the variables of either formula. Agreement on those variables identifies each truth value with the value under the bits of that number, and the bit bridge together with the inclusion puts the number in the second evaluation set, so the second formula is true.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems


/-- **The bijection is an order correspondence, not just a set bijection**: semantic entailment
matches `⊆` of the corresponding `evalSet`s, by the same finitary argument as
`semanticEquiv_iff_evalSet_eq`. -/
theorem entails_iff_evalSet_subset {φ ψ : Formula} :
    Entails φ ψ ↔ evalSet φ ⊆ evalSet ψ := by
  constructor
  · intro h n hn
    rw [mem_evalSet_iff] at hn ⊢
    exact h _ hn
  · intro h v hv
    obtain ⟨n, hn⟩ := exists_bitsOf_agree (vars φ ∪ vars ψ) v
    have h1 : evalV v φ = evalV (fun i => n.testBit i) φ :=
      evalV_eq_of_agree fun i hi => (hn i (Finset.mem_union_left _ hi)).symm
    have h2 : evalV v ψ = evalV (fun i => n.testBit i) ψ :=
      evalV_eq_of_agree fun i hi => (hn i (Finset.mem_union_right _ hi)).symm
    rw [h2, ← mem_evalSet_iff]
    exact h (by rw [mem_evalSet_iff, ← h1]; exact hv)

end DomainTheory.NeighbourhoodSystems
