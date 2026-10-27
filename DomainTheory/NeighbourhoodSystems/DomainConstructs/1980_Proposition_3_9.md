# Proposition 3.9

**PROPOSITION 3.9.** Let neighbourhoods $X_i \in D_0$ and $Y_i \in D_1$ be given for $i < n$. Then the set of $[X_i, Y_i]$ for $i < n$ is consistent in $(D_0 \to D_1)$ iff the following condition holds:

(i) whenever $I \subseteq \{0, 1, \ldots, n-1\}$ and $\{X_i \mid i \in I\}$ is consistent in $D_0$, then $\{Y_i \mid i \in I\}$ must be consistent in $D_1$.

Moreover, when consistency holds, the least approximable mapping $f_0$ belonging to the intersection of the $[X_i, Y_i]$ is defined by:

(ii) $X f_0 Y$ iff $\bigcap \{Y_i \mid X \subseteq X_i\} \subseteq Y$ for $X \in D_0$ and $Y \in D_1$.

*Proof:* Suppose the $[X_i, Y_i]$ are consistent in $(D_0 \to D_1)$. Since the function space is being defined outright as a positive system, consistency means

$$
f \in \bigcap \{[X_i, Y_i] \mid i < n\}
$$

for some $f : D_0 \to D_1$. Now, with $f$ in hand, let us check condition (i). Suppose $\{X_i \mid i \in I\}$ is consistent. This means

$$
x \in \bigcap \{[X_i] \mid i \in I\}
$$

for some $x \in |D_0|$. Suppose $i \in I$, so $x \in [X_i]$. Since $X_i f Y_i$ holds, $f(x) \in [Y_i]$. This means, therefore, that

$$
f(x) \in \bigcap \{[Y_i] \mid i \in I\},
$$

and so $\{Y_i \mid i \in I\}$ is consistent.

For the converse, suppose (i) is the case. We take (ii) as the definition of a mapping and remark that for an arbitrary $X \in D_0$, the set $\{X_i \mid X \subseteq X_i\}$ is automatically consistent in $D_0$. By our assumption, the set $\{Y_i \mid X \subseteq X_i\}$ is therefore consistent. This means that

$$
\bigcap \{Y_i \mid X \subseteq X_i\} \in D_1.
$$

(Keep in mind that $i$ is restricted to those $i < n$, and there are only finitely many neighbourhoods being considered here.) It is thus almost immediate that the relation $f_0$ defined by (ii) satisfies conditions of 2.1 and so is an approximable mapping $f_0 : D_0 \to D_1$. By construction

$$
X_i f_0 Y_i
$$

<!-- page 44 -->

holds trivially for all $i < n$; therefore,

$$
f_0 \in \bigcap \{[X_i, Y_i] \mid i < n\}
$$

and the desired consistency is established.

Finally suppose that $f$ is any mapping in the neighbourhood under discussion; this means $X_i f Y_i$ holds for all $i < n$. Suppose $X f_0 Y$ holds. We have for $X \subseteq X_i$, $X f Y_i$; so

$$
X f \bigcap \{Y_i \mid X \subseteq X_i\} \subseteq Y.
$$

Thus, $X f Y$ follows; hence, as relations, $f_0 \subseteq f$. In other words $f_0$ is the minimal element of the neighbourhood. $\square$

We note that, as a consequence of what we have just proved, when the neighbourhood is consistent, then

$$
\bigcap \{[X_i, Y_i] \mid i < n\} \subseteq [X, Y]
$$

is exactly equivalent to

$$
\bigcap \{Y_i \mid X \subseteq X_i\} \subseteq Y.
$$

Note also that a single neighbourhood $[X_0, Y_0]$ is always consistent since it contains the *constant mapping* $k$ where

$$
X k Y \text{ iff } Y_0 \subseteq Y,
$$

for all $X \in \mathcal{D}_0$ and $Y \in \mathcal{D}_1$. Some other simple observations about these neighbourhoods are just translations of the conditions of Definition 2.1:

$$
[\Delta_0, \Delta_1] = |\mathcal{D}_0 \to \mathcal{D}_1|;
$$

$$
[X, Y] \cap [X, Y'] = [X, Y \cap Y']; \text{ and}
$$

$$
X' \subseteq X \text{ and } Y \subseteq Y' \text{ imply } [X, Y] \subseteq [X', Y'],
$$

for all $X, X' \in \mathcal{D}_0$ and $Y, Y' \in \mathcal{D}_1$. We are now ready to prove the main result about the construct.

**[Proposition_3_9.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Proposition_3_9.lean)**

@import "Proposition_3_9.lean"
