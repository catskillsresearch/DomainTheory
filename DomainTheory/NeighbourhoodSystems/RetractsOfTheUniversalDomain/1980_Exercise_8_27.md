# Exercise 8.27

**EXERCISE 8.27.** (Suggested by James Donahue.)

Finite cartesian products of domains are formed by the $D_0 \times D_1$-construct we have used so often. The problem is to define — computably — some *infinite* cartesian products. In particular, as applied to the universal domain $U$, the combinator `sub` is to be regarded as a finitary projection of $U$ whose fixed points are exactly *all* the finitary projections. A map

$$d = \mathrm{sub} \circ d \circ \mathrm{sub}$$

can be regarded as a *polymorphic type* (because, whenever $t$ is a finitary projection ($=$ type), then so is $d(t)$). The *continuous product* of *all* these types would be the domain of all approximable functions $x$ such that

$$x(t) = d(t)(x(t))$$

for all types $t$. (Why does this equation mean that $x$ is in the product?) Define $\Pi$ as a combinator by

$$\Pi = \lambda d\,\lambda x\,\lambda t.\,\mathrm{sub}(d(\mathrm{sub}(t)))(x(\mathrm{sub}(t))).$$

Show that for $d$ a polymorphic type, $\Pi(d)$ is a type. (Hint: It is easy to check that $\Pi(d)$ is a projection; the problem is to show it is *finitary*.)

<!-- page 151 -->

**[Exercise_8_27.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_27.lean)**

@import "Exercise_8_27.lean"
