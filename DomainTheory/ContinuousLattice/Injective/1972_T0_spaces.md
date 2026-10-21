# T0 spaces

All spaces are $T_0$-spaces, and we begin by defining a class of spaces to be called *injective*.

A **$T_0$-space** (Kolmogorov space) is a topological space in which two distinct points cannot have exactly the same system of open neighbourhoods: whenever $x \neq y$, some open set contains one of them but not the other. Equivalently, if every open neighbourhood of $x$ is a neighbourhood of $y$ and vice versa, then $x = y$. Scott's paper works throughout in this setting rather than assuming Hausdorff separation.

This note is the place to collect $T_0$-specific background and Lean files. Later sections (for example [Specialization](../Specialization/1972_Specialization.md) and [Inverse limits](../InverseLimits/1972_Inverse_limits.md)) still *use* $T_0$ hypotheses where the mathematics requires them, but they do not duplicate the material here.

**Lean 4.** Mathlib names this separation axiom with the typeclass `T0Space`. On a type `X` you already equip with `[TopologicalSpace X]`; `T0Space X` is the Prop-class stating that inseparable points are equal: for all `x y : X`, if `Inseparable x y` then `x = y`. The equivalence with the usual open-set formulation is `t0Space_iff_inseparable`. The class and `Inseparable` live in `Mathlib.Topology.Separation.Basic` and `Mathlib.Topology.Inseparable`.

To **use** a $T_0$ space in a definition or theorem, add `[T0Space X]` next to `[TopologicalSpace X]` on your type variables—the pattern used in [Definition 1.1](1972_Definition_1_1.md) and throughout the library.

To **construct** a $T_0$ topology in this project:

- **Scott topology.** On a complete lattice `D`, the Scott topology is $T_0$; see the proof below (`scottTopology_t0Space`).
- **Subspaces and embeddings.** If `f : X → Y` is an embedding and `Y` is $T_0$, then `X` with the subspace topology is $T_0$ (`Topology.IsEmbedding.t0Space`).
- **Sierpiński space.** `Prop` with the Sierpiński topology is $T_0$; powers and products built from it inherit $T_0$ness (see [Injective spaces](1972_Injective_spaces.md), where `Basic.lean` defines `Sierpinski`).
- **Inverse limits.** Towers of Scott spaces give a $T_0$ inverse-limit topology (`inverseLimit_t0Space` in the inverse-limits development—stated in that chapter, not re-proved here).

When no instance is available yet, prove `T0Space X` by applying the constructor for the class and showing `Inseparable x y → x = y`, or by citing a construction theorem such as `scottTopology_t0Space`.

**Lean 4**

- [ContinuousLattice/Specialization/scottTopology_t0Space.lean](../Specialization/scottTopology_t0Space.lean)
