# Correction

++Correction++ (Added March, 1972). Robin Milner has pointed out to me that there is an error in the remark in the paragraph immediately preceding Proposition 2.5. I was mistaken in saying that if $D$ is a $T_0$-space which becomes a complete lattice under its induced partial ordering, then every set open in the given topology is also open in the induced topology. There are many counterexamples to this statement. Let $D$ be any complete lattice. There are two extreme $T_0$-topologies which will induce the given partial ordering. The smallest such topology has as a sub-base for its open sets those sets of the form:

$$x \in D : x \not\sqsubseteq y.$$

These sets are easily proved to be open in any $T_0$-topology which induces the partial ordering. At the other extreme consider sets of the form:

$$x \in D : y \sqsubseteq x.$$

Such sets will give a base for a $T_0$-topology that is the maximal topology inducing the given partial ordering. Clearly they need not be open in the induced lattice topology; in particular, they may well fail to satisfy conditions (ii) on open sets. To make the remark in question correct, we must thus suppose that the given $T_0$-topology is *contained within* the induced lattice topology. The equation given in the paragraph indicated will then be a sufficient condition for the two topologies to be identical.

The remark was employed in the proof of three different propositions: 2.9, 2.10, and 3.3. In the case of 2.9 one must verify that the product topology is contained within the lattice topology. This need only be done for the basis for the product topology, and for such basic open sets the result needed is obvious. In the case of proposition 2.10 the question concerns a relationship between the topologies of a space and a subspace; the spaces in question are also lattices. Note in passing that a lub in the subspace is generally *larger* in the partial ordering than the corresponding lub relative to the whole space. This puts the inequalities in the wrong direction, and so it is not immediate that a relativized open set for the subspace is open in the lattice topology of the subspace. However, in this case we can appeal to the continuous retraction. Recall that the relativized open sets of the kind that we used in the proof of 2.10 are of the form:

$$U =  z \in D : x < z  \ .$$

Suppose then that $S$ is a directed set, and that using the lub in the sense of $D$ we have

$$\bigsqcup S \in U \ .$$

Referring back to the proof of 2.10 we know that ($S' = S \subseteq D$, but $\bigsqcup S'$ is the join computed in the ambient lattice $D'$)

$$j(\bigsqcup S') = \bigsqcup S \ ,$$

which means that

$$x < j(\bigsqcup S') \ .$$

From this it follows that

$$x < j(z), \text{ some } z \in S \ .$$

Now $j(z) = z$ , and we have what we need. This argument suffices only for a special type of open sets; but these open sets form a base for the topology, and so the argument is quite general.

Turning now to the proof of theorem 2.3 we note that the topology on the function space is simply the *relativized* product topology. There is no difficulty with lubs in this case, because, as we showed in the proof of that theorem, all lubs are calculated pointwise. Thus, it is easy to verify now that the sets open in the product topology are also open in the lattice topology.

**Lean 4**

- [ContinuousLattice/MilnerCorrection/CoarserThanScottTopology.lean](CoarserThanScottTopology.lean)
- [ContinuousLattice/MilnerCorrection/scottLowerSubbasisSet.lean](scottLowerSubbasisSet.lean)
- [ContinuousLattice/MilnerCorrection/scottOpen_of_coarserThanScott.lean](scottOpen_of_coarserThanScott.lean)
- [ContinuousLattice/MilnerCorrection/scottPrincipalUpSet.lean](scottPrincipalUpSet.lean)
- [ContinuousLattice/MilnerCorrection/Basic.lean](Basic.lean)
- [ContinuousLattice/MilnerCorrection.lean](../MilnerCorrection.lean)
