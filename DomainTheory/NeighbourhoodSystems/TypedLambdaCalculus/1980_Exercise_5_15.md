# Exercise 5.15

**EXERCISE 5.15.** (For algebraists.) We can regard $\langle \{0,1\}^*, \Lambda, \cdot \rangle$ as the free semigroup on two generators $0$ and $1$. The powerset $P\{0,1\}^*$ is taken as a domain as in Exercise 4.17. For "words" $e \in \{0,1\}^*$ define

$$
e^* = \{\Lambda, e, e^2, e^3, \ldots, e^n, \ldots\}.
$$

Show that the least fixed point of

$$
z = \{e\} \cdot z \cup \{e'\}
$$

in $P\{0,1\}^*$ is $z = e^* \cdot \{e'\}$.

Show further (as suggested by David Park) that the least solution of

$$
\begin{aligned}
x &= a \cdot x \cup b \cdot y \cup c, \\
y &= b \cdot x \cup a \cdot y \cup d
\end{aligned}
$$

has

$$
x = (a \cup b \cdot a^* \cdot b)^* \cdot (c \cup b \cdot a^* \cdot d),
$$

where the $\{\cdot\}$ has been dropped off $\{a\}$, $\{b\}$ etc., and where the $^*$-notation has been extended to the whole domain, so that $z^* = \Lambda \cup z^* \cdot z$.

(Hint: Apply 5.3.)

<!-- page 91 -->

**[Exercise_5_15.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise_5_15.lean)**

@import "Exercise_5_15.lean"
