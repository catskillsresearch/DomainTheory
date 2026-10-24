module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.entries
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.Fun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.Graph
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.IsApprox
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.mem_entries
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
