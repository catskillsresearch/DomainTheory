# Definition 3.6

We need not enumerate the many corollaries that follow easily now from this result. We mention, however, that composition $f \circ g$ of functions (on continuous lattices) is continuous in the two function variables, where we write

$$
(f \circ g)(x) = f(g(x)).
$$

What will be useful will be to return at this point to a discussion of the injective properties of continuous lattices. If one continuous lattice is a subspace of another it is of course a retract. This relationship between spaces can be given by a pair of continuous maps

$$i : D \to D' \quad \text{and} \quad j : D' \to D,$$

where

$$j \circ i = \text{id}_D = \lambda x : D . x.$$

The composition $i \circ j : D' \to i(D)$ is the retraction onto the subspace corresponding to $D$ under $i$. Now if we have a diagram:

$$
\begin{gathered}
D \xrightarrow[\ j\ ]{i} D' 
f \searrow \qquad \swarrow \tilde{f} = f \circ j 
D''
\end{gathered}
$$

the given continuous $f$ is at once extendable from $D$ to $D'$ by the obvious definition of $\tilde{f}$. This $\tilde{f}$ is not the $\bar{f}$ used in the proof of 2.11, and it will be well to sort out the connections. On one side note that if $f'$ is any function which extends $f$, then we have $f = f' \circ i$. But this implies

$$\tilde{f} = f \circ j = f' \circ i \circ j,$$

which shows that $\tilde{f}$ is a "degraded" version of $f'$. There is one situation where this type of degrading is especially nice.

**3.6 Definition.** A continuous lattice $D$ is said to be a *projection* of a continuous lattice $D'$ iff there are a pair of continuous maps

$$i : D \to D' \quad \text{and} \quad j : D' \to D$$

such that not only

$$j \circ i = \text{id}_D,$$

but also

$$i \circ j \sqsubseteq \text{id}_{D'}.$$

Thus, in case our retraction is a projection, we have $\tilde{f} \sqsubseteq f'$, which means that $\tilde{f}$ is the *minimal* extension of $f \in [D \to D'']$ to a function in $[D' \to D'']$. We will discuss the nature of $\tilde{f}$ in a moment. But before we do we pause to remark that the correspondence $f \rightsquigarrow \tilde{f}$ is *continuous*, and this fact is easily extended.
