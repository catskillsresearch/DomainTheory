# Example 2.3

Note that the right-hand side of (ii) can be written:

$$\uparrow Y \subseteq f(\uparrow X),$$

which can be read as saying that the partial element determined by the neighbourhood $Y$ approximates the function value at the element determined by $X$. This precise relationship of course fits the informal discussion of mapping given earlier. Indeed whenever $x \in [X]$ and $X f Y$ hold, then $f(x) \in [Y]$ always follows, which is another way to construe the mapping character of $f$. Some examples of mappings are now called for.

**EXAMPLE 2.3.** Let $T$ be the neighbourhood system of the two-token domain of Example 1.2. To avoid confusion with some other domains, we will call the two total elements of $|T|$ respectively true and false. There is only one other finite element here, namely $\perp = \text{undefined}$. We often use these elements as indicators of results: true indicates a positive outcome; false, a negative outcome; and $\perp$ indicates that there is not enough information to decide the outcome totally.

Let $B$ be the system for the binary tree as in the last chapter. What we wish to define is an approximable mapping $f : B \to T$. The intuitive idea of the mapping we have in mind is that the binary sequence is being read from left to right, and we are counting the number of 0's seen before the first 1 is encountered. We then test the parity of this count; if it is even, the output is true; if not, false. Using a suggestive informal notation with three dots, some results of the function that does the counting and testing can be written as:

$$
\begin{aligned}
f(0000101\dots) &= \text{true} \\
f(1101110\dots) &= \text{true} \\
f(0111011\dots) &= \text{false} \\
f(0000000\dots) &= \perp.
\end{aligned}
$$

The last equation is necessary, because $0000000$ as a partial element cannot be counted as either even or odd since it can have inconsistent extensions:

$$
\begin{aligned}
0000000\,\perp &\sqsubseteq 00000001\,\perp \\
0000000\,\perp &\sqsubseteq 000000000001\,\perp.
\end{aligned}
$$

So, as far as $f$ is concerned, a plain string of 0's is indefinite. The same answer holds if the 0's go on infinitely.

To be more precise we want

$$
\begin{aligned}
f(0^n 1\,\perp) &= \text{true} && \text{if } n \text{ is even;} \\
&= \text{false} && \text{if } n \text{ is odd.}
\end{aligned}
$$

As a binary relation $f \subseteq B \times T$ we will have

$$
X f Y \text{ iff } Y \in \perp \text{ or } X \sqsubseteq 0^n 1 \Delta \text{ for some } n \in \mathbf{N} \text{ and either } n \text{ is even and } Y \in \text{true or } n \text{ is odd and } Y \in \text{false.}
$$

It should be checked that 2.1(i)–(ii) are satisfied. $\square$

**Lean 4**

- [NeighbourhoodSystems/MappingsBetweenDomains/Example23.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/Basic.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/Basic.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/T.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/T.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/botElt.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/botElt.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/botElt_le.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/botElt_le.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/eq_botElt_of_le.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/eq_botElt_of_le.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/falseElt.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/falseElt.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/parityMap.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/parityMap.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/parityMap_rel_cone.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/parityMap_rel_cone.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/parityMap_toElementMap_mem.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/parityMap_toElementMap_mem.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/parityMap_toElementMap_sigmaElt.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/parityMap_toElementMap_sigmaElt.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan_append.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan_append.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan_append_falseFalse.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan_append_falseFalse.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan_append_falseTrue.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan_append_falseTrue.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan_append_true.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan_append_true.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan_false.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan_false.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan_nil.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan_nil.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan_true.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/scan_true.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/trueElt.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/trueElt.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/valElt.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/valElt.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example23/valElt_scan_mono.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example23/valElt_scan_mono.lean)
