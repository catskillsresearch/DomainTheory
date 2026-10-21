/-ai
σ_j of the singleton of the code of (j, m) is the singleton of the code of (j, m + 1).

Extensionality. A witness in the singleton has index m by injectivity of pairing, so the element is the successor code. That successor code is witnessed by the index m.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sigmaJ_succ_singleton (j m : ℕ) :
    sigmaJ j {pair j m} = ({pair j (m + 1)} : Pomega) := by
  ext p
  constructor
  · intro ⟨k, heq, hp⟩
    have : k = m := (pair_inj hp).2
    subst this
    simp [heq]
  · intro hp
    exact ⟨m, hp.symm, by simp⟩

end DomainTheory.DataTypesAsLattices
