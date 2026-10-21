# Definition

**DEFINITION.** An element $a \in \mathbf{P}\omega$ is called a *closure operation* iff it satisfies:

$$\mathbf{I} \subseteq a = a \circ a.$$

We see by definition that a closure operation is not only continuous, but it is also a retract. This is reasonable since the closure of the closure of a subset must be equal to the closure. To say of a function that $\mathbf{I} \subseteq a$ means that $x \subseteq a(x)$ for all $x \in \mathbf{P}\omega$. In other words, every set is contained in its closure. (Note that closures are opposite to the “projections”, those retracts where $a \subseteq \mathbf{I}$.) Among examples of closure operations we find $\mathbf{I}$ and $\mathbf{T}$; the first has the most closed sets (fixed points). The second has the least. (Note that $\mathbf{T} = \omega$ always is a fixed point of a closure operation; $\mathbf{T} = \lambda x.\,\mathbf{T}$ is thus the most trivial closure operation.) The examples **fun**, **open**, and **int** of § 4 are all closure operations (cf. (4.1), (4.6), (4.7)). We remarked that **fun** is a retract, but the reader should prove in addition:

$$(5.1) \quad u \subseteq \lambda x.\, u(x),$$

for all $u \in \mathbf{P}\omega$ (cf. Theorem 1.2). We note that this fact can be rewritten in the language of retracts as:

$$(5.2) \quad \mathbf{I} \subseteq \mathbf{I} \circ\to \mathbf{I},$$

the significance of which will emerge after we develop a bit of the theory of closure operations.

Unfortunately the natural definition of the retract **bool** does not yield a closure operation. In this section we adopt this modification:

$$(5.3) \quad \mathbf{boool} = \lambda u.\, u \supset 0,\, \mathbf{T} + 1.$$

The closed sets of **boool** are $\bot$, $0$, $\mathbf{T} + 1$, and $\mathbf{T}$. Note that with any closure operation $a$, the function value $a(x)$ is the least closed set (fixed point of $a$) including as a subset the given set $x$. Thus given any family $\mathscr{C} \subseteq \mathbf{P}\omega$ of “closed” sets which is closed under the intersection of subfamilies, if we define

$$(5.4) \quad a(x) = \bigcap \{y \in \mathscr{C} \mid x \subseteq y\},$$
then this will be a closure operation *provided* it is continuous. This remark makes it easy to check that certain functions are closure operations if we can spot easily the family $\mathscr{C}$ of fixed points.

Alas, the “natural” definition of ordered pairs (cf. (2.21)) leads to projections rather than closures. Here we must choose another:

$$(5.5) \quad [x, y] = \{2n \mid n \in x\} \cup \{2m + 1 \mid m \in y\},$$

with these inverse functions:

$$(5.6) \quad [u]_0 = \{n \mid 2n \in u\},$$

$$(5.7) \quad [u]_1 = \{m \mid 2m + 1 \in u\}.$$

We shall find that the main advantage of these equations lies in the obvious equation:

$$(5.8) \quad u = [[u]_0, [u]_1],$$

which is not true for the other pairing functions. Of course we have:

$$(5.9) \quad [[x, y]]_0 = x,$$

$$(5.10) \quad [[x, y]]_1 = y.$$

We shall not extend the idea of these new functions to triples and sequences, though it is clear what to do.

Abstractly, an *algebraic lattice* is a complete lattice in which the isolated points are dense. An *isolated* (sometimes called: *compact*) point in a lattice is one that is not the limit (sup or l.u.b.) of any directed family of its proper subelements. This definition works in continuous lattices, but more generally it is better to say that if the isolated point is *contained in* a sup, then it is also contained in a finite subsup (a sup of a finite selection of elements out of the given sup). In the case of the lattice of subgroups of a group, the isolated ones are the finitely generated subgroups. The isolated points of $\mathbf{P}\omega$ are the finite sets $e_n$. To say that isolated points are *dense* means that every element in the lattice is the sup of the isolated points it contains. The sequel to Theorem 4.1 for closure operations relates them to algebraic lattices.
