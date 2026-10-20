/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.eraseTag_Z_finite
import DomainTheory.DataTypesAsLattices.Functionality.eraseTag_Z_finite_union


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
