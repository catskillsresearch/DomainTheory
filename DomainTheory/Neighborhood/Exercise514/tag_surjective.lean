/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise513
import Mathlib.Data.List.Basic
import DomainTheory.Neighborhood.Exercise514.Basic
import DomainTheory.Neighborhood.Exercise514.num_succ_left_gt


namespace DomainTheory.Neighborhood.Exercise514

open DomainTheory.Neighborhood.Exercise513






/-- **The tag is onto**: every `c : ℕ` decodes as some `tag ns m`. Strong induction on `c`,
decreasing via `num_succ_left_gt`. -/
theorem tag_surjective (c : ℕ) : ∃ ns m, tag ns m = c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
      obtain ⟨a, b, hab⟩ : ∃ a b, num a b = c :=
        ⟨(unnum c).1, (unnum c).2, numP_unnum c⟩
      cases a with
      | zero => exact ⟨[], b, hab⟩
      | succ k =>
          have hlt : b < c := by rw [← hab]; exact num_succ_left_gt k b
          obtain ⟨ns, m, hns⟩ := ih b hlt
          exact ⟨k :: ns, m, by rw [tag_cons, hns]; exact hab⟩

end DomainTheory.Neighborhood.Exercise514
