# Exercise 1.23

**EXERCISE 1.23.** Suppose that the neighbourhood system $D$ is countable, say,

$$
D = \{X_0, X_1, X_2, \ldots, X_n, \ldots\}.
$$

Suppose further that the property of consistency of finite sequences of neighbourhoods is decidable (or "effectively known"). Then the following sequence is well defined:

$$
\begin{aligned}
Y_0 &= X_0 \\
Y_{n+1} &= X_{n+1}, \text{ if this set is consistent with } Y_0, Y_1, \ldots, Y_n; \\
&= Y_n, \text{ if not.}
\end{aligned}
$$

Show that $\{Y_0, Y_1, \ldots, Y_n, \ldots\}$ is a total element of $|D|$. (Hint: Show first that $Y_0, Y_1, \ldots, Y_{n-1}$ is consistent for all $n$.) In such a system show that all filters can be determined by sequences.

**Lean 4**

- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise123.lean](Exercise123.lean)
