# Definition

**DEFINITION.** An element $a \in \mathbf{P}\omega$ is called a *retract* iff it satisfies the equation $a = a \circ a$.

Of course the $\circ$-notation is used for functional composition in the standard way:

$$(4.5) \quad u \circ v = \lambda x.\, u(v(x)).$$

And it is quite simple to prove that each of the three combinators in (4.1)–(4.3) is a retract according to the definition. But what is the point?

Consider $\mathbf{fun}$. No matter what $u \in \mathbf{P}\omega$ we take, $\mathbf{fun}(u)$ is (the graph of) a *function*. And if $u$ already is (the graph of) a function, then $u = \mathbf{fun}(u)$. That is to say, the range of $\mathbf{fun}$ is the same as the set of fixed points of $\mathbf{fun}$ is the same as the set of all (graphs of) functions. Any mapping $a$ whose range and fixed-point set coincide satisfies $a = a \circ a$, and conversely. A retract is a mapping which “retracts” the whole space onto its range and which is the identity mapping on its range. That is the import of the equation $a = a \circ a$. Strictly speaking, the range is the retract and the mapping is the retraction, but for us the mapping is more important. (Note, however, that distinct retracts can have the same range.) We let the mapping stand in for the range.

Thus the combinator **fun** represents in itself the concept of a *function* (continuous function on $\mathbf{P}\omega$ into $\mathbf{P}\omega$). Similarly **pair** represents the idea of a *pair* and **bool** the idea of being a boolean value as an element of $\{\bot, 0, 1, \top\}$, since we must think in the multiple-valued mode. What is curious (and, as we shall see, useful) is that all these retracts which are defining subspaces are at the same time elements of $\mathbf{P}\omega$.
