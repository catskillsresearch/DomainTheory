/-ai
Every set u of natural numbers is contained in the graph of the application of u.

Surjectivity of the tag writes a code in u as the tag of some list and some output. That same list witnesses that the output belongs to the application of u at the entries of the list, because each entry belongs to the list and the tag, rewritten as the original code, lies in u.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_surjective

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513












/-- **`graph ∘ fun ⊇ λx.x`**: `u ⊆ Graph (Fun u)`. -/
theorem id_le_Graph_Fun (u : Set ℕ) : u ⊆ Graph (Fun u) := by
  intro c hc
  obtain ⟨ns, m, hceq⟩ := tag_surjective c
  refine ⟨ns, m, hceq.symm, ?_⟩
  exact ⟨ns, fun n hn => hn, by rw [hceq]; exact hc⟩

end DomainTheory.NeighbourhoodSystems.Exercise514
