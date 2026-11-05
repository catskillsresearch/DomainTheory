# Directed union of ideal elements

Given an increasing sequence $x_0 \subseteq x_1 \subseteq \cdots$ of ideal elements, the directed union $\bigcup_n x_n$ is again an ideal element: a neighbourhood belongs to the join precisely when it belongs to some $x_n$. It is the least upper bound of the sequence in the approximation order. (Monotonicity is needed so that neighbourhoods drawn from different stages still have a common later stage in which their intersection may be formed.)

**[iUnion.lean](iUnion.lean)**

@import "iUnion.lean"
