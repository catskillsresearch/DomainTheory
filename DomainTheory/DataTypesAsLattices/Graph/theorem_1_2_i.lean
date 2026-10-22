/-ai
Scott's Theorem 1.2 (i) states that if f is Scott continuous, then applying the graph of f recovers f.

Function extensionality and extensionality of sets reduce the claim to membership of a number m at an argument x. A pair in the graph lies in f at a basic element contained in x, and monotonicity of f puts m in f(x). Conversely, continuity rewrites membership in f(x) as membership in the Scott union of f, which supplies a basic element contained in x at which m lies in f, and that pair lies in the graph.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 1.2 (i).** `fun(graph(f)) = f` when `f` is continuous. -/
theorem theorem_1_2_i {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf (graph f) = f := by
  funext x
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    obtain ⟨n', m', heq, hm'⟩ := hp
    obtain ⟨rfl, rfl⟩ := pair_inj heq
    exact isScottContinuous_monotone hf hn hm'
  · intro hm
    have : m ∈ scottUnion f x := by
      rw [← hf.out x]; exact hm
    obtain ⟨n, hn, hmn⟩ := mem_scottUnion.mp this
    exact ⟨n, hn, ⟨n, m, rfl, hmn⟩⟩

end DomainTheory.DataTypesAsLattices
