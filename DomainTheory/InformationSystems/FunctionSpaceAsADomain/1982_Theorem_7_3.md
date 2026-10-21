# Theorem 7.3

**THEOREM 7.3.** Let $\mathbf{A}$ be an information system. Then there is a unique operator, the **least fixed-point operator**, such that

(i) $\mathrm{fix} : (\mathbf{A} \to \mathbf{A}) \to \mathbf{A}$; and,

for all approximable mappings $f : \mathbf{A} \to \mathbf{A}$, we have:

(ii) $f(\mathrm{fix}(f)) \subseteq \mathrm{fix}(f)$; and

(iii) for all $x \in |\mathbf{A}|$, if $f(x) \subseteq x$, then $\mathrm{fix}(f) \subseteq x$.

Moreover, for this operator, condition (ii) is an equality.

*Proof.* This is a well-known result—especially the fact that the conditions above uniquely determine the operator. The only question is the existence of the operator. The inclusion of condition (ii) gives the hint, for $\mathrm{fix}(f)$ is the least solution of $f(x) \subseteq x$. Suppose $x$ is any such element, then if $u \subseteq x$ and $u \ f \ v$ hold, it follows that $v \subseteq x$. Now, since $\emptyset \subseteq x$ always holds, if we wish to form the least $x$, we start with $\emptyset$ and just follow it under the action of $f$.

Specifically, we define $\mathrm{fix}(f)$ to be the union of all $v \in \mathrm{Con}_{\mathbf{A}}$ for which there exist a sequence $u_0, \ldots, u_n \in \mathrm{Con}_{\mathbf{A}}$ where:

(1) $u_0 = \emptyset$;

(2) $u_i \ f \ u_{i+1}$ for all $i < n$; and

(3) $u_n = v$.
Because $f$ is approximable, it is clear that $\mathrm{fix}\, f$ is closed under entailment. To prove that it is consistent, suppose both $v$ and $v'$ belong to the sets thrown into the union. We have to show that $v \cup v'$ is consistent and also is thrown in. Consider the two sequences $u_0, \ldots, u_n \in \mathrm{Con}_{\mathbf{A}}$ and $u'_0, \ldots, u'_n \in \mathrm{Con}_{\mathbf{A}}$ that are responsible for putting $v$ and $v'$ in. It is without loss of generality that we assume they are of the same length, since we can always add lots of $\emptyset$'s onto the front of the shorter one and still satisfy (1)–(3). Now one just argues by induction on $i$ that the sequence of unions $u_i \cup u'_i$ satisfies (1)–(3) with respect to $v \cup v'$.

But why is $\mathrm{fix}$ approximable? The method of proof is to replace $f$ by $\bar{w}$ in (2) above, and to use the condition that there exists a sequence satisfying (1)–(3) as defining a relation between sets $w \in \mathrm{Con}_{\mathbf{A} \to \mathbf{A}}$ and sets $v \in \mathrm{Con}_{\mathbf{A}}$. It is not difficult to prove that this is an approximable mapping in the sense of the official definition. Clearly this relation determines $\mathrm{fix}$ as an operator. $\blacksquare$
