# Example 4.3

The reader may have noticed that we used recursion in the proof of 4.1 (we had to define $f^n$ for all $n \in \mathbf{N}$). But 4.1 and 4.2 can be used to justify definitions by recursion on a large number of domains — definitions where the process of iteration is far from being as straightforward. In discussing this point, let us start with some basic examples.

**EXAMPLE 4.3.** The infinite generalization of our original example 1.2 is the system

$$
N = \{ \{n\} \mid n \in \mathbf{N} \} \cup \{ \mathbf{N} \}.
$$

The total elements are clearly in a one-one correspondence with the integers in $\mathbf{N}$. We can apply the construction of Exercise 3.16 to obtain a domain

$$
F = N^\infty.
$$

So we already know quite a bit about this domain — but it has a much more familiar presentation.

Let $\Phi$ be the set of all *finite partial functions* $\varphi \subseteq \mathbf{N} \times \mathbf{N}$ (that is, finite sets of ordered pairs of integers where, if $(n,m) \in \varphi$ and $(n,m') \in \varphi$, then $m = m'$). Define

$$
\uparrow \varphi = \{ \psi \in \Phi \mid \varphi \subseteq \psi \}.
$$

Consider the neighbourhood system

$$
F' = \{ \uparrow \varphi \mid \varphi \in \Phi \}.
$$

It is an easy exercise to show that $F$ and $F'$ are isomorphic and that the elements of these domains correspond exactly to the (possibly infinite) *partial functions* $\pi \subseteq \mathbf{N} \times \mathbf{N}$. Moreover, the *total* elements just correspond to the *total* functions $\tau : \mathbf{N} \to \mathbf{N}$ ("function" in the ordinary, set-theoretical sense of the word).

Another easy exercise is to show that the domains

$$
F \text{ and } (\mathbf{N} \to \mathbf{N})
$$

by our definitions are *NOT* isomorphic; though the two domains are closely related. We can define a mapping
$$
\mathrm{val} : F \times N \to N
$$

by the relationship

$$
\uparrow \phi \cup \{n\}\ \mathrm{val}\ \{m\} \quad \text{iff} \quad (n, m) \in \phi.
$$

(Of course $\mathrm{val}$ has to relate other neighbourhoods such as:

$$
\uparrow \phi \cup N\ \mathrm{val}\ N,
$$

but these are all.) It is then simple to prove that if $\pi \in |F|$ is regarded as a partial function $\pi : N \to N$ and if for $n \in N$ we define $\hat{n} \in |N|$ by

$$
\hat{n} = \{ \{n\}, N \},
$$

then we have

$$
\mathrm{val}(\pi, \hat{n}) = \widehat{\pi(n)}, \text{ if } \pi \text{ is defined at } n;
$$

$$
\qquad\qquad\qquad\qquad = \{N\}, \text{ otherwise.}
$$

(Remember that $\{N\} \in |N|$ is the "undefined" element.) This means that

$$
\mathrm{curry}(\mathrm{val}) : F \to (N \to N)
$$

is a one-one function on elements. (The rather slight trouble with $(N \to N)$ is that it has *more* elements than $F$.)

So much for the construction of $F$, we now wish to consider mappings

$$
f : F \to F
$$

and their uses. Consider the possibility

$$
f(\pi)(n) = 0, \qquad\qquad\qquad\qquad \text{if } n = 0;
$$

$$
\qquad\qquad\qquad = \pi(n-1) + n-1, \text{ if } n > 0.
$$

If $\pi$ were a total function, then $f(\pi)$ would be total. But if $\pi$ is partial, and if it is, say, undefined at $k$, then $f(\pi)$ becomes undefined at $k + 1$. Note that $f(\pi)$ is always defined at $0$. Note, too, that $f$ is an approximable mapping because it is completely determined by what it does to finite (partial) functions. Indeed,

$$
f(\pi) = \bigcup \{ f(\phi) \mid \phi \subseteq \pi \},
$$
where $\phi$ ranges over $\Phi$.

Well, we have proved that every approximable map of a domain into itself has a (*least*) fixed point. What is the least fixed point of this $f$? Suppose $\sigma = f(\sigma)$. Then $\sigma(0) = 0$, and

$$
\sigma(n + 1) = f(\sigma)(n + 1)
$$

$$
= \sigma(n) + n.
$$

By induction, then

$$
\sigma(n) = \sum_{i < n} i
$$

and $\sigma$ is a total function. (Therefore, $f$ has a *unique* fixed point.)

Actually, we can make the procedure more systematic by defining as fixed points elements of $(N \to N)$ rather than $F$. In the first place we have $\hat{0} \in |N|$, and from now on we will not distinguish between $n$ and $\hat{n}$. Next we have two mappings:

$$
\mathrm{succ}, \mathrm{pred} : N \to N
$$

where, as approximable mappings we have

$$
X\ \mathrm{succ}\ Y\ \mathrm{iff}\ \exists n \in N.\ n \in X\ \mathrm{and}\ n + 1 \in Y,
$$

$$
X\ \mathrm{pred}\ Y\ \mathrm{iff}\ \exists n \in N.\ n + 1 \in X\ \mathrm{and}\ n \in Y,
$$

for all $X, Y \in N$. This is *correct*, but what we mean in more understandable terms is:

$$
\mathrm{succ}(n) = n + 1;
$$

$$
\mathrm{pred}(n) = n - 1,\ \text{if}\ n > 0;
$$

$$
\qquad\qquad = \bot,\ \text{if}\ n = 0.
$$

Here, $n$ has been identified with $\hat{n} \in |N|$ and $\bot = \{N\} \in |N|$. Moreover, we have a mapping

$$
\mathrm{zero} : N \to T
$$

which is such that

$$
\mathrm{zero}(n) = \text{true, if } n = 0;
$$

$$
\qquad\qquad = \text{false, if } n > 0.
$$

The *structured domain*

$$
\langle N, 0, \mathrm{succ}, \mathrm{pred}, \mathrm{zero} \rangle
$$
can be called "THE domain of integers" for our present theory. We shall meet many other structured domains in the sequel.

Now the iterated summation function $\sigma$ can be completely characterized — as a map $\sigma : N \to N$ rather than as an element $\sigma \in |F|$ — by the following equation:

$$
\sigma(n) = \mathrm{cond}(\mathrm{zero}(n),\ 0,\ \sigma(\mathrm{pred}(n)) + \mathrm{pred}(n)).
$$

The only problem is that we have not defined $+ : N \times N \to N$. (A direct definition is left to the reader; general remarks are given later.) But $+$ could be any function of two variables in order to make the point about the form of the definition of $\sigma$. Remember

$$
\mathrm{cond} : T \times N \times N \to N,
$$

as defined in Exercise 3.26. We do not put cond in as part of the structure of $N$ because (as should be clear from 3.26) it is part of the structure of $T$.

The above equation for $\sigma$ is properly called a *functional equation*; it will be written as a fixed-point equation in Lecture V when we have the notation for the $\lambda$-calculus. $\square$

**Lean 4**

- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N_bot_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N_bot_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N_master.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N_master.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/T.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/T.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/constLiftN.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/constLiftN.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/constLiftN_bot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/constLiftN_bot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/constLiftN_natElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/constLiftN_natElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/memN.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/memN.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/memN_singleton.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/memN_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/memN_univ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/memN_univ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/mem_natElem_iff.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/mem_natElem_iff.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/natElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/natElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/nestedOrDisjoint.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/nestedOrDisjoint.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_bot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_bot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_natElem_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_natElem_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_natElem_zero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_natElem_zero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_succMap_natElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_succMap_natElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predVal.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predVal.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/singleton_nat_inj.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/singleton_nat_inj.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/singleton_ne_univ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/singleton_ne_univ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/succMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/succMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/succMap_bot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/succMap_bot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/succMap_natElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/succMap_natElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/univ_ne_singleton.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/univ_ne_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroElt.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroElt.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap_bot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap_bot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap_natElem_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap_natElem_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap_natElem_zero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap_natElem_zero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroVal.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroVal.lean)
