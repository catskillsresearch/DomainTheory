
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sigmaJ_of_no_tag {j : ℕ} {u : Pomega}
    (hu : ∀ k, pair j k ∉ u) :
    sigmaJ j u = botElem := by
  ext p
  constructor
  · intro ⟨k, _hp, hk⟩
    exact (hu k hk).elim
  · simp [botElem]

end DomainTheory.DataTypesAsLattices
