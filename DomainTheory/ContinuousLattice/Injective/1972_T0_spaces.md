# T0 spaces

A **$T_0$-space** (Kolmogorov space) is a topological space in which two distinct points cannot have exactly the same system of open neighbourhoods: whenever $x \neq y$, some open set contains one of them but not the other. Equivalently, if every open neighbourhood of $x$ is a neighbourhood of $y$ and vice versa, then $x = y$. Scott's paper works throughout in this setting rather than assuming Hausdorff separation.  Lean 4 Mathlib names this separation axiom with the typeclass `T0Space`. On a type `X` you already equip with `[TopologicalSpace X]`; `T0Space X` is the Prop-class stating that inseparable points are equal: for all `x y : X`, if `Inseparable x y` then `x = y`. The equivalence with the usual open-set formulation is `t0Space_iff_inseparable`. The class and `Inseparable` live in `Mathlib.Topology.Separation.Basic` and `Mathlib.Topology.Inseparable`.  To **use** a $T_0$ space in a definition or theorem, add `[T0Space X]` next to `[TopologicalSpace X]` on your type variables—the pattern used in [Definition 1.1](1972_Definition_1_1.md) and throughout the library.

We begin by defining a class of $T_0$-spaces spaces to be called *injective*.

To **construct** a $T_0$ topology in this project:

- **Scott topology.** On a complete lattice `D`, the Scott topology is $T_0$. The proof is `scottTopology_t0Space`, linked from [Specialization](../Specialization/1972_Specialization.md) after the specialization order it uses.
- **Subspaces and embeddings.** If `f : X → Y` is an embedding and `Y` is $T_0$, then `X` with the subspace topology is $T_0$ (`Topology.IsEmbedding.t0Space`).
- **Sierpiński space.** `Prop` with the Sierpiński topology is $T_0$; powers and products built from it inherit $T_0$ness (see [Proposition 1.2](1972_Proposition_1_2.md), where `Sierpinski` is defined and shown injective).
- **Inverse limits.** Towers of Scott spaces give a $T_0$ inverse-limit topology (`inverseLimit_t0Space` in the inverse-limits development—stated in that chapter, not re-proved here).

When no instance is available yet, prove `T0Space X` by applying the constructor for the class and showing `Inseparable x y → x = y`. The Scott-topology instance is the theorem `scottTopology_t0Space` in [Specialization](../Specialization/1972_Specialization.md).
