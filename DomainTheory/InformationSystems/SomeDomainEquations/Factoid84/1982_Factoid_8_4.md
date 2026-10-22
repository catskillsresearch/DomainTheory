# Factoid 8.4

*A domain of domains.* Not many details can be presented here, but we would also like to remark that even domains can be made into a domain. One way of getting an idea of how this is possible is to note that since subdomains of $\mathbf{U}$ correspond to certain kinds of functions on $\mathbf{U}$, and since the function space of $\mathbf{U}$ is also a subdomain of $\mathbf{U}$, it might be suspected that the subdomains of $\mathbf{U}$ form a single subdomain of $\mathbf{U}$.

That is a fairly sophisticated way of reaching the conclusion (and many details have to be worked out). A more elementary approach would be just to ask what it means to give a finite amount of information about a domain. For the sake of uniformity, suppose that the data objects of the possible domain are drawn from the non-negative integers, and that we conventionally use $0$ for $\Delta$. Then to give a finite amount of information about a domain is—roughly—to specify a finite part of $\mathrm{Con}$ and a finite part of $\vdash$. To make the formulation easier, we will reserve for $1$ a rôle like the one recently played by $\nabla$. What the specifications will boil down to is pairs $(u, v)$ of finite sets of integers used as data objects to convey one piece of information about an entailment relation.

But hold, entailment relations are very closely connected to approximable mappings. Indeed, we remarked before that the identity function as an approximable mapping on a domain is just represented as the underlying entailment relation itself. Suppose we take as our domain the domain of all sets of integers. It is a powerset, so call it $\mathbf{P}$. That is to say, the integers are the data objects, all finite sets are consistent, and the entailment relation is the minimal possible one. (As far as elements go, an arbitrary set of integers is equal to the union of all its finite subsets, which means that the elements of the domain are in a one-one correspondence with the arbitrary sets of integers.) The question is: which approximable mappings on $\mathbf{P}$ into itself correspond to entailment relations on the integers as data objects?

The answer can be expressed most succinctly using our standard notation. If we think of $r : \mathbf{P} \to \mathbf{P}$ as a relation between finite sets in the usual way, then to say that $r$ is reflexive is to say:

(1) $I_{\mathbf{P}} \subseteq r$.

To say that $r$ is transitive is to say:

(2) $r \circ r = r$.
To say that for $r$ the object $0$ plays at being $\Delta$ is to say:

$$(3) \quad \bar{0} \subseteq r(\bot),$$

where in general $\bar{n}$ is short for $\{n\}$ in the domain $\mathbf{P}$. Then, to say that $1$ plays at being a rogue object is to say:

$$(4) \quad \top = r(\bar{1}).$$

Finally, to say that $1$ is an inconsistent object that has to be excluded is to say:

$$(5) \quad \bar{1} \not\subseteq r(\bar{0}).$$

That's it. The collection of approximable mappings satisfying (1)–(5) gives us all the entailment relations we need. Condition (5) is a consistency condition, and for $r$ the consistent finite sets $u$ are those such that $\bar{1} \not\subseteq r(\bar{u})$. What we are asserting is that the totality of $r$ satisfying (1)–(5) forms the elements of a domain—one that has been derived from $(\mathbf{P} \to \mathbf{P})$ in a way similar to the way we derived $\mathbf{U}$ from $\mathbf{V}$ above.

Having made domains into a domain, the next step is to see how constructs on domain (i.e. functors) can be made into approximable mappings. But the retelling and development of that story will have to wait for another publication along with the very interesting chapter on powerdomains. I only hope the ground covered here makes the theory of domains seem more elementary and more natural. ■

**Lean 4**

- [InformationSystems/SomeDomainEquations/Factoid84/PEnt.lean](PEnt.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/P.lean](P.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/IdemApprox.lean](IdemApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/P_AllConsistent.lean](P_AllConsistent.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/ReflApprox.lean](ReflApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/bar.lean](bar.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/barElement.lean](barElement.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/ConsistentApprox.lean](ConsistentApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/botElement.lean](botElement.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/BotApprox.lean](BotApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatRel_of_mem_one.lean](flatRel_of_mem_one.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/mem_botElement.lean](mem_botElement.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/barElement_zero_eq_bot.lean](barElement_zero_eq_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/not_RogueApprox_idMap.lean](not_RogueApprox_idMap.lean)
- [InformationSystems/SomeDomainEquations/Factoid84.lean](../Factoid84.lean)
- [InformationSystems.lean](../../../InformationSystems.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/scottCon_empty_iff_consistent.lean](scottCon_empty_iff_consistent.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/topElement.lean](topElement.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/RogueApprox.lean](RogueApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/IsDomainApprox.lean](IsDomainApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/DomainApprox.lean](DomainApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatRel.lean](flatRel.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatRel_empty.lean](flatRel_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatMap.lean](flatMap.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatMap_idem.lean](flatMap_idem.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatMap_refl.lean](flatMap_refl.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/mem_barElement.lean](mem_barElement.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/BotApprox_any.lean](BotApprox_any.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatMap_consistent.lean](flatMap_consistent.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/mem_topElement.lean](mem_topElement.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatMap_toElement_of_mem_one.lean](flatMap_toElement_of_mem_one.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatMap_rogue.lean](flatMap_rogue.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatMap_isDomain.lean](flatMap_isDomain.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatDomainApprox.lean](flatDomainApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/scottCon.lean](scottCon.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/Basic.lean](Basic.lean)
