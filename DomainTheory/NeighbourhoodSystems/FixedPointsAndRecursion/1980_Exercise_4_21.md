# Exercise 4.21

**EXERCISE 4.21.** Show that the less-than-or-equal-to relation $\ell \subseteq \mathbf{N} \times \mathbf{N}$ is uniquely determined by the fixed point equation

$$
\ell = \{(n,n) \mid n \in \mathbf{N}\} \cup \{(n, m^+) \mid (n, m) \in \ell\}.
$$

Consider the structured set $\langle P\mathbf{N}, \mathbf{N}, {}^+ \rangle$ where, as before, $x^+ = \{n^+ \mid n \in x\}$.

What is the unique function $[\cdot] : \mathbf{N} \to P\mathbf{N}$ given by 4.13(3)? Prove that the structures $\langle \mathbf{N}, 0, {}^+ \rangle$ and $\langle [m], m, {}^+ \rangle$ are uniquely isomorphic for each $m \in \mathbf{N}$, and connect the isomorphism with ordinary addition of integers. Can the same be done for multiplication? (Hint: Consider the fixed-point equation

$$
n \cdot \mathbf{N} = \{0\} \cup \{n + m \mid m \in n \cdot \mathbf{N}\},
$$

where $n \in \mathbf{N}$ is fixed.)

**[Exercise_4_21.lean](Exercise_4_21.lean)**

@import "Exercise_4_21.lean"
