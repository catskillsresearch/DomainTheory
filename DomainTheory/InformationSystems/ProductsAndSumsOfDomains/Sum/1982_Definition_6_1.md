# Definition 6.1

**DEFINITION 6.1.** Let $\mathbf{A}$ and $\mathbf{B}$ be two information systems. By $\mathbf{A} \times \mathbf{B}$, the *product system*, we understand the system where:

(i) $D_{\mathbf{A} \times \mathbf{B}} = \{(X, \Delta_{\mathbf{B}}) \mid X \in D_{\mathbf{A}}\} \cup \{(\Delta_{\mathbf{A}}, Y) \mid Y \in D_{\mathbf{B}}\}$;

(ii) $\Delta_{\mathbf{A} \times \mathbf{B}} = (\Delta_{\mathbf{A}}, \Delta_{\mathbf{B}})$;

(iii) $u \in \mathrm{Con}_{\mathbf{A} \times \mathbf{B}}$ iff $\mathrm{fst}\, u \in \mathrm{Con}_{\mathbf{A}}$ and $\mathrm{snd}\, u \in \mathrm{Con}_{\mathbf{B}}$;

(iv') $u \vdash_{\mathbf{A} \times \mathbf{B}} (X', \Delta_{\mathbf{B}})$ iff $\mathrm{fst}\, u \vdash_{\mathbf{A}} X'$; and

(iv'') $u \vdash_{\mathbf{A} \times \mathbf{B}} (\Delta_{\mathbf{A}}, Y')$ iff $\mathrm{snd}\, u \vdash_{\mathbf{B}} Y'$;

where, in (iii), $u$ is any finite subset of $D_{\mathbf{A} \times \mathbf{B}}$, in (iv') and (iv''), $u \in \mathrm{Con}_{\mathbf{A} \times \mathbf{B}}$, and we let:

$$\mathrm{fst}\, u = \{X \in D_{\mathbf{A}} \mid (X, \Delta_{\mathbf{B}}) \in u\}, \text{ and}$$

$$\mathrm{snd}\, u = \{Y \in D_{\mathbf{B}} \mid (\Delta_{\mathbf{A}}, Y) \in u\}. \quad \blacksquare$$

Note that in 6.1(i) the two sets in the union are just two copies of $D_{\mathbf{A}}$ and $D_{\mathbf{B}}$, respectively. There is a shared member, however, the object $(\Delta_{\mathbf{A}}, \Delta_{\mathbf{B}})$, which is indeed the least informative data object—whether it is looked at from the point of view of $\mathbf{A}$ or of $\mathbf{B}$. We could have used all the pairs $(X, Y)$, but if we did, the consistent set $\{(X, Y)\}$ would be deductively equivalent to the set $\{(X, \Delta_{\mathbf{B}}), (\Delta_{\mathbf{A}}, Y)\}$ according to the definition of $\vdash_{\mathbf{A} \times \mathbf{B}}$, and so there is not much point in having this redundancy. Strictly speaking, we should not make these remarks until we have actually verified that 6.1 is indeed a proper definition.
