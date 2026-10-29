# Proposition 7.12

**PROPOSITION 7.12.** The mapping

$$\lambda x_0, \dots, x_{n-1}.\, \{x_0, \dots, x_{n-1}\} : D^n \to \mathbb{P} D$$

is approximable and is computable if $D$ is effectively given. Moreover, the map $\lambda x.\, \{x\}$ shows that $D \trianglelefteq \mathbb{P} D$, and we also have the law:

$$\{x_0, \dots, x_{n-1}\} = \{x_0\} \cap \dots \cap \{x_{n-1}\}$$

as an intersection of filters.

*Proof* : The second part shows that everything reduces to $\lambda x.\, \{x\}$. We see that

$$X_k\ (\lambda x.\, \{x\})\ \bigcup_{i<q} (\uparrow X_{n_i}) \text{ iff } \exists i < q.\, X_k \sqsubseteq X_{n_i}.$$

Thus, $\lambda x.\, \{x\}$ is an approximable mapping and is computable in the effectively given case.

The proof of the law can be reduced to the special case

$$\{x\} \cap \{y\} = \{x, y\}$$

for the sake of illustration. In terms of finite elements of the two domains $D$ and $\mathbb{P} D$ we find

$$\{\uparrow X\} = \uparrow\uparrow X,$$

and so,

$$\begin{aligned}
\{\uparrow X\} \cap \{\uparrow Y\} &= \uparrow\uparrow X \cap \uparrow\uparrow Y \\
&= \uparrow(\uparrow X \cup \uparrow Y) \\
&= \{\uparrow X, \uparrow Y\}.
\end{aligned}$$

An equation between approximable functions that checks for finite elements also holds for all elements.

Finally, we note that

$$D \cong D^\dagger \trianglelefteq \mathbb{P} D$$

<!-- page 130 -->

and that the isomorphism involved is just $\lambda x.\,\{x\}$ by what we saw on the finite elements. $\square$

Further combinators on the power domain are given in the exercises.

**[Proposition_7_12.lean](Proposition_7_12.lean)**

@import "Proposition_7_12.lean"
