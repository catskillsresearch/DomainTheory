# Example 4.4

**EXAMPLE 4.4.** The domain $C$ of finite or infinite binary sequences mentioned in Exercise 2.21 may be regarded as a generalization of $N$. This can be made plain by saying how we wish to regard $C$ as a structured domain. To do this we should recall what $C$ is as a neighbourhood system. In the first place

$$
B = \{ \sigma\Sigma^* \mid \sigma \in \Sigma^* \}
$$

where $\Sigma = \{0, 1\}$. To form the system $C$ we have

$$
C = B \cup \{ \{\sigma\} \mid \sigma \in \Sigma^* \}.
$$

The total elements of $B$ correspond to *infinite binary sequences*; while the total elements of $C$ to *finite or infinite sequences*. To simplify notation let us write for $\sigma \in \Sigma^*$

$$
\sigma = \uparrow \{\sigma\} \quad \text{(a total element);}
$$

$$
\sigma\perp = \uparrow \sigma\Sigma^* \quad \text{(a partial element).}
$$
In other words we identify $\sigma$ with the corresponding total element in $|C|$.

We wish now to think of $C$ as a structured domain seen as a kind of generalization of $N$. The empty sequence $\Lambda$ will play the rôle of $0 \in |N|$; the map succ has two different analogues for $C$, however. Just as for $B$ we define for $x \in |C|$ and $\sigma \in \Sigma^*$:

$$
\sigma x = \{ Y \mid \sigma X \subseteq Y \text{ some } X \in x \},
$$

where of course now $X$ and $Y$ range over $C$. It should be checked that $\sigma \tau$ has the right meaning whether we think of $\tau \in \Sigma^*$ or $\tau \in |C|$. The two "successor" mappings we are looking for are

$$
x \mapsto 0x \quad \text{and} \quad x \mapsto 1x.
$$

All the maps $x \mapsto \sigma x$ can be obtained as compositions of these iterated as many times as needed.

Here are two questions which we now should ask:

<u>What plays the rôle of pred?</u>

The mapping will be called **tail**, and it is characterized by:

$$
\mathrm{tail}(0x) = x,
$$

$$
\mathrm{tail}(1x) = x, \text{ and}
$$

$$
\mathrm{tail}(\Lambda) = \perp.
$$

It is left to the reader to show that **tail** exists as an approximable mapping.

<u>What plays the rôle of zero?</u>

The answer is not unique, because in $C$ there are several distinctions that have to be made; in fact we will define three maps:

$$
\mathrm{empty}, \mathrm{zero}, \mathrm{one} : C \to T
$$

where the three maps take on truth-values to distinguish various kinds of elements in $|C|$ as follows:
$$
\begin{aligned}
\mathrm{empty}\,(\Lambda) &= \mathrm{true}, \\
\mathrm{empty}\,(0x) &= \mathrm{false}, \\
\mathrm{empty}\,(1x) &= \mathrm{false}, \\
\mathrm{zero}\,(\Lambda) &= \mathrm{false} \\
\mathrm{zero}\,(0x) &= \mathrm{true} \\
\mathrm{zero}\,(1x) &= \mathrm{false} \\
\mathrm{one}\,(\Lambda) &= \mathrm{false} \\
\mathrm{one}\,(0x) &= \mathrm{false} \\
\mathrm{one}\,(1x) &= \mathrm{true}.
\end{aligned}
$$

Again, it is an exercise to show these are approximable. The structured domain is therefore

$$
\langle C, \Lambda, 0, 1, \mathrm{tail}, \mathrm{empty}, \mathrm{zero}, \mathrm{one} \rangle.
$$

Note that we have changed the meaning of some of the symbols in passing from $N$ to $C$. Note too that there is a confusion between $0$ as an element and $0$ as the map $x \mapsto 0x$. There are just too few symbols! In any case this is only an example and not a philosophy of life, so the reader can be expected not to suffer too much.

An example of a definition of an *element* of $|C|$ by a fixed-point equation is:

$$
a = 0\,1\,a.
$$

This equation has one and only one solution in $|C|$, the infinite sequence that alternates 0's and 1's. Note that $a$ is also characterized by:

$$
a = 0101a.
$$

Another element is

$$
b = 010\,b,
$$

which is quite different from $a$.

An example of a *map* in $|C \to C|$ has the characterization

$$
\begin{aligned}
d(\Lambda) &= \Lambda \\
d(0x) &= 00d(x), \quad \text{and} \\
d(1x) &= 11d(x).
\end{aligned}
$$

We can write:
$$
\begin{aligned}
d(x) &= \mathrm{cond}(\mathrm{empty}(x),\, \Lambda, \\
&\qquad\qquad \mathrm{cond}(\mathrm{zero}(x),\, 00d(\mathrm{tail}(x)),\, 11d(\mathrm{tail}(x)))).
\end{aligned}
$$

As we shall see in due course, this can be regarded as a fixed-point definition of $d$.

An example of a map in $|C \times C \to C|$ was suggested in 2.21. We can write:

$$
\begin{aligned}
xy &= \mathrm{cond}(\mathrm{empty}(x),\, y, \\
&\qquad\qquad \mathrm{cond}(\mathrm{zero}(x),\, 0(\mathrm{tail}(x)\,y),\, 1(\mathrm{tail}(x)\,y))).
\end{aligned}
$$

It should be checked that this equation exactly characterizes the intended mapping. $\square$

The examples we have given with $N$ and $C$ are examples of definitions of functions by *recursion*. The literal meaning of “recursion” is “running backwards”, and a look at the equations for our examples will show that the functions are characterized by giving their values either *outright* (e.g. at $0$ or at $\Lambda$) or at *earlier* arguments (e.g. at $\mathrm{pred}(x)$ or at $\mathrm{tail}(x)$). The reader should keep in mind that a recursive “definition” is not really a definition in the sense of *explicit definition* but rather is a characterization; a theorem has to be proved to show that such functions exist. Now we have a general definition of domain and a general theorem on fixed points and a general construction of function-space domain; THEREFORE, we know that there are solutions to our equations PROVIDED THAT the variables range over elements of a domain and that the other, given functions that appear in the equations are already known to be approximable (continuous). This proviso is very important, and we shall remark on it time after time.

But, as is well known, recursion also can be done over sets like $\mathbf{N}$, and we should examine now the connection between the familiar kind of recursion and what we are doing over domains. Of course, one simple connection is already provided by the way we regard $\mathbf{N}$ as a subset of $N$. But there are other useful connections that can be employed in a way that may seem more direct.

**Lean 4**

- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/C.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/C.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/C_master.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/C_master.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/C_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/C_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/altElt.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/altElt.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/altElt_eq.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/altElt_eq.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/consMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/consMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/consMap_strBot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/consMap_strBot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/consMap_strElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/consMap_strElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC_cone.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC_cone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC_prepend.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC_prepend.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC_singleton.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/nestedOrDisjoint.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/nestedOrDisjoint.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/prepend_mono.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/prepend_mono.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/prepend_singleton.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/prepend_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/prepend_subset_self.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/prepend_subset_self.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/singleton_cone_nd.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/singleton_cone_nd.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/singleton_subset_cone.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/singleton_subset_cone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/strBot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/strBot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/strElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/strElem.lean)
