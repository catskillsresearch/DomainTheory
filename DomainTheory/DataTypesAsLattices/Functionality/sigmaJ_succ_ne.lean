/-ai
If j and j' are distinct, then σ_j of the singleton of the code of (j', m) is bottom.

A member of the image would require the code of (j, k) to equal the code of (j', m), so injectivity of pairing would give j = j', which is excluded. Bottom has no members.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


























theorem sigmaJ_succ_ne (j j' m : ℕ) (hne : j ≠ j') :
    sigmaJ j {pair j' m} = botElem := by
  ext p
  constructor
  · intro ⟨k, _hk, hp⟩
    have : pair j k = pair j' m := by
      simpa [Set.mem_singleton_iff] using hp
    exact (hne (pair_inj this).1).elim
  · intro hp
    simp [botElem] at hp

end DomainTheory.DataTypesAsLattices
