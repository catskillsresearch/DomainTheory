# Exercise 5.13

**EXERCISE 5.13.** Prove the existence of a one-one function $\mathrm{num} : \mathbf{N} \times \mathbf{N} \to \mathbf{N}$ such that

$$
\mathrm{num}(0, 0) = 0;
$$

$$
\mathrm{num}(n, m+1) = \mathrm{num}(n+1, m) + 1;
$$

$$
\mathrm{num}(n+1, 0) = \mathrm{num}(0, n) + 1.
$$

Draw a picture (i.e. an infinite matrix) for the function and find a closed form for its values, if possible. Use the function to prove the isomorphism of the domains

$$
P\mathbf{N},\ P(\mathbf{N} \times \mathbf{N}),\ P\mathbf{N} \times P\mathbf{N}.
$$

**Lean 4**

- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise513.lean](Exercise513.lean)
