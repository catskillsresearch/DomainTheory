
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
