/-ai
Scott 1976, (7.19). The m-fold iterate of the union of the graphs of the tagged successors at j and at j', started at the union of the singletons of (j, 0) and (j', 0), equals the union of the singletons of (j, m) and (j', m).

If the tags agree, the unions collapse and the claim is the equal-tag rule. If the tags differ, the argument inducts on m. The zero step is reflexivity. The successor step rewrites the iterate by equation (2.9), uses the inductive hypothesis and two applications of the tagged successor, then the union rule for distinct tags and the symmetric union rule with the union commuted.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_app
public import DomainTheory.DataTypesAsLattices.Functionality.eq_7_18_eq
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_pair_union

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (7.19).**
Independent successor powers advance both tagged atoms in lockstep. -/
theorem eq_7_19 (j j' m : ℕ) :
    Z m (graph (sigmaJ j) ∪ graph (sigmaJ j'))
        (({pair j 0} : Pomega) ∪ {pair j' 0}) =
      ({pair j m} : Pomega) ∪ {pair j' m} := by
  by_cases h : j = j'
  · subst j'
    simp only [Set.union_self]
    exact eq_7_18_eq j m
  · induction m with
    | zero => rfl
    | succ m ih =>
      rw [Z, eq_2_9, ih, sigmaJ_app, sigmaJ_app,
        sigmaJ_pair_union j j' m h]
      rw [show sigmaJ j' (({pair j m} : Pomega) ∪ {pair j' m}) =
          ({pair j' (m + 1)} : Pomega) by
        simpa [Set.union_comm] using sigmaJ_pair_union j' j m (Ne.symm h)]

end DomainTheory.DataTypesAsLattices
