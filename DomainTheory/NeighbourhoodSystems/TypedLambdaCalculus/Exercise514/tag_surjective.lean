/-ai
The tag is surjective: every natural number is the tag of some finite list and some output.

The argument is strong induction on the number. The inverse of the pairing writes it as a pair (a, b). If a is zero, the empty list with output b is a decoding. If a is a successor k, the strict increase of the pairing puts b below the number, so the inductive hypothesis decodes b, and consing k recovers the original number by the cons equation of the tag.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.num_succ_left_gt

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513






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

end DomainTheory.NeighbourhoodSystems.Exercise514
