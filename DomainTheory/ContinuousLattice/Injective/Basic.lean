/-ai
Scott's §1 on injective T₀-spaces: extension along subspace embeddings, products, retracts, and embedding into a Sierpiński power.
ai-/
module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens
public import DomainTheory.ContinuousLattice.Injective.IsRetractSubspace
public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace

@[expose] public section

/-!
# Injective spaces (Scott 1972, §1)

Scott's §1 introduces *injective* `T₀`-spaces — those with the extension property for
continuous maps along subspace embeddings — and shows the two-point Sierpiński space is
injective, that injectivity is preserved by products and by retracts, and (the embedding
theorem) that every `T₀`-space embeds in a power of the Sierpiński space.

## Main definitions / results

* `InjectiveSpace` — Scott's Definition 1.1.
* `Sierpinski`, `isInjectiveSpace_sierpinski`, `proposition_1_2` — Scott's Proposition 1.2.
* `proposition_1_3` … `proposition_1_5` — Scott's Propositions 1.3–1.5.
* `corollary_1_6`, `corollary_1_7` — Scott's Corollaries 1.6 and 1.7.
-/
