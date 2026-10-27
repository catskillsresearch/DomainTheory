# Proposition 8.2

**PROPOSITION 8.2.** If $D \triangleleft E$ and if $a : E \to E$ is defined by

$$X \ a \ Z \quad \text{iff} \quad \exists Y \in D.\ X \subseteq Y \subseteq Z$$

for all $X, Z \in E$, then $a$ is a retraction and $|D|$ is isomorphic to the fixed-point set of $a$, the set $\{y \in |E| \mid a(y) = y\}$, under inclusion.

*Proof:* That $a$ is an approximable mapping is a direct consequence of Definition 6.10. Indeed, in the notation of Proposition 6.12, we have

$$a = i \circ j,$$

and this is another proof that $a$ is approximable. This remark is also convenient, since we know from 6.10

$$j \circ i = I_D.$$

Therefore, we find:

$$a \circ a = i \circ j \circ i \circ j = i \circ j = a;$$

and so $a$ is a retraction.

We can also employ $i$ and $j$ to give the isomorphism on $|D|$. If $x \in |D|$, then $i(x) \in |E|$ and we calculate:

<!-- page 136 -->

$$a(i(x)) = i \circ j \circ i(x) = i(x).$$

Thus, $i(x)$ belongs to the fixed-point set of $a$. In the other direction, if $a(y) = y$, then $i(j(y)) = y$. But $j(y) \in |D|$, so $i$ maps $|D|$ one-one and onto the fixed-point set of $a$. As $i$ and $j$ are monotone, the map is an isomorphism with respect to $\sqsubseteq$. $\square$

Not every retraction comes from a relationship like $D \triangleleft E$; in fact, we can see from the definition of $a$ above that $a \sqsubseteq 1_E$. But, as is indicated in Exercise 8.11, even this condition is not sufficient to characterize the kind of retractions provided by 8.2. The characterization is as follows.

**[Proposition_8_2.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition_8_2.lean)**

@import "Proposition_8_2.lean"
