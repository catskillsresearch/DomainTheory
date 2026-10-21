# Definition

**DEFINITION.** A continuous function $f$ of $k$-variables is *computable* iff the relationship

$$m \in f(e_{n_0})(e_{n_1}) \cdots (e_{n_{k-1}})$$

is recursively enumerable (r.e.) in the integer variables $m, n_0, n_1, \dots, n_{k-1}$.

If $q$ is a partial recursive function in the usual sense, then we can regard it as a mapping $q : \omega \to \omega \cup \{\bot\}$, where $q(n) = \bot$ means that $q$ is undefined at $n$. Saying that $q$ is partial recursive is just to say that $m \in q(n)$ is r.e. as a relation in $n$ and $m$. It is easy to see that this is in turn equivalent to the recursive enumerability of the relationship $m \in \hat{q}(e_n)$; and so our definition is formally a generalization of the usual one. But it is also intuitively reasonable. To “compute” $y = f(x)$, in the one-variable case, we proceed by enumeration. First we begin the enumeration of all finite subsets $e_n \subseteq x$. For each of these $f$ starts up an enumeration of the set $f(e_n)$; so we sit back and observe which $m \in f(e_n)$ by enumeration. The totality of all such $m$ for all $e_n \subseteq x$ forms in the end the set $y$.
