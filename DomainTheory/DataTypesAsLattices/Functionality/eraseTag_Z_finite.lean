/-ai
Erasing the tag one more than the maximum of p and q from the m-fold iterate of the finite element e p started at e q leaves that iterate unchanged.

Membership extensionality. A member of the erased set already lies in the iterate. A member of the iterate remains after erasure because the finite-iterate rule says it is not the pair of that tag with any index.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Z_finite_no_tag

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem eraseTag_Z_finite (p q m : ℕ) :
    eraseTag (max p q + 1) (Z m (e p) (e q)) = Z m (e p) (e q) := by
  ext k
  constructor
  · exact fun hk => hk.1
  · intro hk
    exact ⟨hk, fun r hkr => Z_finite_no_tag p q m r (hkr ▸ hk)⟩

end DomainTheory.DataTypesAsLattices
