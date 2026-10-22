/-ai
For an approximable map f and any set x, applying the graph of f to x returns f(x).

The two inclusions are proved separately. If an output comes from a list of entries in x whose tag lies in the graph, injectivity of the tag matches that list and output with a witness that the output belongs to f of those entries, and monotonicity of f lifts the inclusion of the entries into x. Conversely, finite approximation supplies a list of entries from x on which f already produces the output, and that same tag lies in the graph.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_injective

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513


/-- **`fun ∘ graph = λf.f`** for continuous `f`: `Fun (Graph f) x = f x`. -/
theorem Fun_Graph {f : Set ℕ → Set ℕ} (hf : IsApprox f) (x : Set ℕ) :
    Fun (Graph f) x = f x := by
  apply Set.Subset.antisymm
  · intro m hm
    obtain ⟨ns, hsub, htag⟩ := hm
    obtain ⟨ns', m', heq, hmem⟩ := htag
    obtain ⟨hns, hmm⟩ := tag_injective heq
    subst hns; subst hmm
    have hsubset : entries ns ⊆ x := fun n hn => hsub n hn
    exact hf.1 hsubset hmem
  · intro m hm
    obtain ⟨ns, hsub, hmem⟩ := hf.2 x m hm
    exact ⟨ns, hsub, ns, m, rfl, hmem⟩

end DomainTheory.NeighbourhoodSystems.Exercise514
