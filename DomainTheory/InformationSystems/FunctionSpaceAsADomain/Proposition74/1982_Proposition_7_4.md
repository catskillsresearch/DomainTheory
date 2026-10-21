# Proposition 7.4

The result above not only proves that every approximable mapping of the form $f : \mathbf{A} \to \mathbf{A}$ has a fixed point as an element of $\mathbf{A}$, but that the association of the least fixed point is itself an approximable operator. The formulation makes essential use of the partial ordering of the domains, but Gordon Plotkin noticed as an exercise that the characterization of the operator can be given entirely by equations.

**PROPOSITION 7.4.** *The least fixed-point operator is uniquely determined by the following three conditions:*

(i) $\mathrm{fix}_{\mathbf{A}} : (\mathbf{A} \to \mathbf{A}) \to \mathbf{A}$, *for all systems* $\mathbf{A}$;

(ii) $\mathrm{fix}_{\mathbf{A}}(f) = f(\mathrm{fix}_{\mathbf{A}}(f))$, *for all* $f : \mathbf{A} \to \mathbf{A}$; *and*

(iii) $h(\mathrm{fix}_{\mathbf{A}}(f)) = \mathrm{fix}_{\mathbf{B}}(g)$, *whenever* $f : \mathbf{A} \to \mathbf{A}$, $g : \mathbf{B} \to \mathbf{B}$, $h : \mathbf{A} \to \mathbf{B}$, *provided that* $h \circ f = g \circ h$ *and* $h(\bot_{\mathbf{A}}) = \bot_{\mathbf{B}}$. $\blacksquare$

*Remarks on the space of strict mappings.* In 7.4 and many other places we have had occasion to make use of mappings that take the bottom element of one domain over to the bottom element of the other domain. Such mappings are called *strict mappings* because they take a strict view of having empty input. As notation we might write

$$f : \mathbf{A} \to_{\blacksquare} \mathbf{B}$$

to mean that $f$ is a strict approximable mapping (i.e. $f(\bot_{\mathbf{A}}) = \bot_{\mathbf{B}}$). The totality of domains and strict mappings forms an interesting category in itself, but it is best used in connection with the full category of all approximable mappings.

The collection of strict mappings forms a domain, too. The way to see this is to refer back to Definition 7.1 and add an additional clause ruling out non-strict mappings as inconsistent. What has to be added to 7.1(iii) is the conjunct on the right-hand side to the effect that if the condition $\emptyset \vdash_{\mathbf{A}} \bigcup \{u_i \mid i \in I\}$ holds, then $\emptyset \vdash_{\mathbf{B}} \bigcup \{v_i \mid i \in I\}$ holds too. By the same arguments we used before, it follows that this is the appropriate system for the domain of strict mappings. We can denote it by $(\mathbf{A} \to_{\blacksquare} \mathbf{B})$.

There is also a useful operator

$$\mathrm{strict} : (\mathbf{A} \to \mathbf{B}) \to (\mathbf{A} \to_{\blacksquare} \mathbf{B})$$
defined by the condition that for $f : \mathbf{A} \to \mathbf{B}$ we have:

$$u \,\mathit{strict}(f)\, v \text{ iff either } \emptyset \vdash_{\mathbf{B}} v \text{ or } \emptyset \not\vdash_{\mathbf{A}} u \text{ and } u f v,$$

for all $u \in \mathrm{Con}_{\mathbf{A}}$ and $v \in \mathrm{Con}_{\mathbf{B}}$. This operator converts every approximable mapping into the largest strict mapping contained within it.

Since every strict mapping is an approximable mapping, there is also an obvious operator going the other way. The pair of operators shows that $\mathbf{A} \to_s \mathbf{B}$ as a domain is what is called a *retract* of $\mathbf{A} \to \mathbf{B}$. There is an interesting theory of this kind of relationship between domains, but we cannot enter into it here.

As a very small application of the use of strict mappings, we remark that the following two domains are isomorphic:

$$\mathbf{A} \times \mathbf{A} \cong (\mathbf{BOOL} \to_s \mathbf{A}).$$

The mapping from right to left is called the *conditional operator*, cond, and we have for all elements $x, y \in |\mathbf{A}|$ and $t \in |\mathbf{BOOL}|$

$$\mathrm{cond}(x, y)(t) = \begin{cases} x, & \text{if } t = \text{true}, \\ y, & \text{if } t = \text{false}. \end{cases} \blacksquare$$

**Lean 4**

- [InformationSystems/FunctionSpaceAsADomain/Proposition74.lean](../Proposition74.lean)
- [InformationSystems/FunctionSpaceAsADomain/Proposition74/Basic.lean](Basic.lean)
- [InformationSystems/FunctionSpaceAsADomain/Proposition74/fixChain_toElement_le_fix.lean](fixChain_toElement_le_fix.lean)
- [InformationSystems/FunctionSpaceAsADomain/Proposition74/fixElement_le_toElement_fix.lean](fixElement_le_toElement_fix.lean)
- [InformationSystems/FunctionSpaceAsADomain/Proposition74/idMap_botElement.lean](idMap_botElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Proposition74/proposition_7_4_ii.lean](proposition_7_4_ii.lean)
- [InformationSystems/FunctionSpaceAsADomain/Proposition74/proposition_7_4_iii.lean](proposition_7_4_iii.lean)
- [InformationSystems/FunctionSpaceAsADomain/Proposition74/proposition_7_4_unique.lean](proposition_7_4_unique.lean)
- [InformationSystems/FunctionSpaceAsADomain/Proposition74/toElement_comp_fix_le.lean](toElement_comp_fix_le.lean)
- [InformationSystems/FunctionSpaceAsADomain/Proposition74/toElement_fix_le_fixElement.lean](toElement_fix_le_fixElement.lean)
