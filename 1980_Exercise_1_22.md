# Exercise 1.22

$$
\bigcap_{i < n} [ X_i ] \neq \emptyset.
$$

**EXERCISE 1.22.** (For topologists). Show that the neighbourhoods $[X]$ for $X \in \mathcal{D}$ make $|\mathcal{D}|$ into a topological space where the open subsets $\mathcal{U} \subseteq |\mathcal{D}|$ can be characterized by the following two conditions:

(i) whenever $x \in \mathcal{U}$ and $x \sqsubseteq y \in |\mathcal{D}|$, then $y \in \mathcal{U}$; and

(ii) whenever $x \in \mathcal{U}$, then $[X] \in \mathcal{U}$ for some $X \in x$.

Prove also that the inclusion relation on $|\mathcal{D}|$ can be defined topologically as:

(iii) $x \sqsubseteq y$ iff for all open $\mathcal{U} \subseteq |\mathcal{D}|$, if $x \in \mathcal{U}$ then $y \in \mathcal{U}$.
Is $|D|$ ever a Hausdorff space?

Show that if $(x_n)_{n=0}^{\infty}$ is a sequence of elements of $|D|$ with $x_n \subseteq x_{n+1}$ for all $n$, then

$$
\bigcup_{n=0}^{\infty} x_n
$$

is not only in $|D|$ but is a topological limit point of the sequence. Show that any element $x$ is a limit point of the set $\{\uparrow X \mid X \in x\}$. Are there other limit points?

**Lean 4**

- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/IsOpenFilter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/IsOpenFilter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/basicOpen.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/basicOpen.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_basicOpen.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_basicOpen.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_iff_isOpenFilter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_iff_isOpenFilter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_iff_upper_basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_iff_upper_basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_isUpperSet.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_isUpperSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/le_iff_isOpen_imp.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/le_iff_isOpen_imp.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/mem_basicOpen.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/mem_basicOpen.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/specializes_iff_le.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/specializes_iff_le.lean)
