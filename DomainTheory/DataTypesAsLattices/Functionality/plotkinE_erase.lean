/-ai
If u and v are related by the Plotkin equivalence at the fresh tag max(p, q) + 1, then erasing that tag from u and from v gives the same set.

Discard the goodness hypotheses and induct on the generated equivalence. A generating step, for some m, identifies the plain iterate with the iterate that has the fresh pair adjoined, in either order, and the two erasure lemmas agree on those sets. Reflexivity is the identity, symmetry reverses the inductive equality, and transitivity composes the two inductive equalities.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.eraseTag_Z_finite
public import DomainTheory.DataTypesAsLattices.Functionality.eraseTag_Z_finite_union

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem plotkinE_erase {p q : ℕ} {u v : Pomega}
    (h : (plotkinE p q (max p q + 1)).rel u v) :
    eraseTag (max p q + 1) u = eraseTag (max p q + 1) v := by
  rcases h with ⟨_hu, _hv, h⟩
  clear _hu _hv
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨m, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · rw [eraseTag_Z_finite, eraseTag_Z_finite_union]
      · rw [eraseTag_Z_finite, eraseTag_Z_finite_union]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end DomainTheory.DataTypesAsLattices
