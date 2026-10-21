/-ai
If j and j' are distinct, then σ_j of the union of the singleton of the code of (j, m) and the singleton of the code of (j', m) is the singleton of the code of (j, m + 1).

Extensionality. A witness from the first singleton forces the index to be m, hence the element to be the successor code. A witness from the second singleton forces j = j' by injectivity of pairing, which is excluded. The successor code itself is recovered from the first singleton at the index m.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sigmaJ_pair_union (j j' m : ℕ) (hne : j ≠ j') :
    sigmaJ j (({pair j m} : Pomega) ∪ {pair j' m}) =
      ({pair j (m + 1)} : Pomega) := by
  ext p
  constructor
  · intro ⟨k, hp, hk⟩
    rcases hk with hk | hk
    · have hkm : k = m := (pair_inj hk).2
      subst k
      simpa using hp.symm
    · have hj : j = j' := (pair_inj hk).1
      exact (hne hj).elim
  · intro hp
    exact ⟨m, hp.symm, Or.inl (by simp)⟩

end DomainTheory.DataTypesAsLattices
