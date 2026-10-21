# Definition 6.3

We turn now to the definition and properties of sums of domains.

**DEFINITION 6.3.** Let $\mathbf{A}$ and $\mathbf{B}$ be two information systems. By $\mathbf{A} + \mathbf{B}$, the *separated sum system*, we understand the system where, after choosing some convenient object $\Delta$ belonging neither to $D_{\mathbf{A}}$ nor to $D_{\mathbf{B}}$, we have:

(i) $D_{\mathbf{A}+\mathbf{B}} = \{(X, \Delta) \mid X \in D_{\mathbf{A}}\} \cup \{(\Delta, Y) \mid Y \in D_{\mathbf{B}}\} \cup \{(\Delta, \Delta)\}$;

(ii) $\Delta_{\mathbf{A}+\mathbf{B}} = (\Delta, \Delta)$;

(iii) $u \in \mathrm{Con}_{\mathbf{A}+\mathbf{B}}$ iff either $\mathrm{lft}\, u \in \mathrm{Con}_{\mathbf{A}}$ and $\mathrm{rht}\, u = \emptyset$ or $\mathrm{lft}\, u = \emptyset$ and $\mathrm{rht}\, u \in \mathrm{Con}_{\mathbf{B}}$;

(iv') $u \vdash_{\mathbf{A}+\mathbf{B}} (X', \Delta)$ iff $\mathrm{lft}\, u \neq \emptyset$ and $\mathrm{lft}\, u \vdash_{\mathbf{A}} X'$;

(iv'') $u \vdash_{\mathbf{A}+\mathbf{B}} (\Delta, Y')$ iff $\mathrm{rht}\, u \neq \emptyset$ and $\mathrm{rht}\, u \vdash_{\mathbf{B}} Y'$; and

(iv''') $u \vdash_{\mathbf{A}+\mathbf{B}} (\Delta, \Delta)$ always holds,

where, in (iii), $u$ is any finite subset of $D_{\mathbf{A}+\mathbf{B}}$, in (iv')–(iv'''), $u \in \mathrm{Con}_{\mathbf{A}+\mathbf{B}}$, and we let:

$$\mathrm{lft}\, u = \{X \in D_{\mathbf{A}} \mid (X, \Delta) \in u\}, \quad \mathrm{rht}\, u = \{Y \in D_{\mathbf{B}} \mid (\Delta, Y) \in u\}.$$

$\blacksquare$

The plan of the sum definition is very similar to that for product, except that (1) for reasons to be made clear in examples, the parts do not share the least informative element (i.e. the data objects $(\Delta_{\mathbf{A}}, \Delta)$, $(\Delta, \Delta_{\mathbf{B}})$, and $(\Delta, \Delta)$ are inequivalent in this system), and (2) instead of defining consistency and entailment in a conjunctive way, these notions are defined disjunctively. The effect of these changes over Definition 6.1 is to produce a system $\mathbf{A} + \mathbf{B}$ whose elements divide into disjoint copies of those of $\mathbf{A}$ and $\mathbf{B}$ (plus an extra element $\perp_{\mathbf{A}+\mathbf{B}}$). These remarks can be made more precise in the following way:
