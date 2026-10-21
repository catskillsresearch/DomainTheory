# Definition 1.1

DEFINITION 1.1. A family $\mathcal{D}$ of subsets of a given set $\Delta$ is called a *neighbourhood system* (over $\Delta$) iff it is a non-empty family closed under the intersection of finite consistent sequences of neighbourhoods. That is to say, $\mathcal{D}$ must fulfill these two conditions:

(i) $\Delta \in \mathcal{D}$;

(ii) whenever $X$, $Y$, $Z \in \mathcal{D}$ and $Z \subseteq X \cap Y$, then $X \cap Y \in \mathcal{D}$. $\square$
We remark that by convention $\Delta$ corresponds to the intersection of an empty sequence of neighbourhoods; in particular,

$$
\bigcap_{i < n} X_i = \Delta, \text{ if } n = 0;
$$

$$
= \left(\bigcap_{i < n-1} X_i\right) \cap X_{n-1}, \text{ if } n > 0.
$$

Of course, from (ii), we can extend the intersection property to any finite sequence. Consequently, we can say $X_0, \dots, X_{n-1}$ is consistent in $\mathcal{D}$ iff

$$
\bigcap_{i < n} X_i \in \mathcal{D}.
$$

Some examples will help us understand the notions better.
