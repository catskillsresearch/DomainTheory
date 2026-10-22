# A first example

**A first example.** Suppose we let $D$ be the set of non-negative integers, where we think of an integer $n$ as an abbreviation of the proposition $n \le x$. Here $x$ is a yet-to-be-determined element, about which one proposition gives only a little information. We can identify $\Delta$ with $0$, and take $\mathrm{Con}$ to be the set of all finite subsets of $D$. The entailment relation can be defined formally in the way suggested by the intuitive reading of the data objects:

$$\{n_0, \dots, n_{k-1}\} \vdash m \quad\text{iff either } m = 0 \text{ or } m \le n_i \text{ for some } i < k.$$

(Remember to think of the same possible $x$ on both sides of the $\vdash$.) That $\vdash$ is an entailment relation in the sense of our axioms is clear. ■

**Lean 4**

- [InformationSystems/InformationSystems/lowerBoundEnt.lean](lowerBoundEnt.lean)
- [InformationSystems/InformationSystems/Factoid24.lean](Factoid24.lean)
