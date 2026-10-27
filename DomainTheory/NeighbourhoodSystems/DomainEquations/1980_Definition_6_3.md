# Definition 6.3

**DEFINITION 6.3.** A *functor* on a category (into itself) associates with every domain $X$ in the category another domain $T(X)$ and to every map

$$
f : X \to Y
$$

another map

$$
T(f) : T(X) \to T(Y)
$$

<!-- page 102 -->

in such a way that identity maps and compositions are preserved:

$$
T(I_X) = I_{T(X)}, \text{ and}
$$

$$
T(g \circ f) = T(g) \circ T(f),
$$

whenever $f : X \to Y$ and $g : Y \to Z$. $\square$

In the example from 6.1 we have not checked how the special **T** is a functor. The hint is that whenever $f : X \to Y$, then there is a map

$$
f \times f : X \times X \to Y \times Y.
$$

But there is also a map

$$
I_D + f \times f : D + (X \times X) \to D + (Y \times Y)
$$

and this suggests the definition of $T(f)$. The details are left to the exercises. Note that the map $T(f)$ just suggested is always strict, so **T** is a functor also for the category of strict maps.

One good reason for a little of the category-theoretic language is that the next definition becomes very neat indeed.

**[Definition_6_3.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition_6_3.lean)**

@import "Definition_6_3.lean"
