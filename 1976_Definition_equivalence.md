# Definition

**DEFINITION.** A (restricted) *equivalence relation* on $\mathbf{P}\omega$ is a symmetric and transitive relation on $\mathbf{P}\omega$.

Such relations are restricted because they are only reflexive on their domains—which are the same as their ranges—and these are the subsets with which the relations are concerned. We shall write $x \, A \, y$ for $\langle x, y \rangle \in A$ and $x : A$ for $x \, A \, x$. What we assume about these relations is the following:

$$(7.2) \quad x \, A \, y \text{ implies } y \, A \, x.$$

$$(7.3) \quad x \, A \, y \text{ and } y \, A \, z \text{ imply } x \, A \, z.$$

In case $a$ is a retract, we introduce an equivalence relation to correspond:

$$(7.4) \quad E_a = \{\langle x, x \rangle \mid x : a\}.$$

This is the identity relation restricted to the range of $a$. Such relations (for obvious reasons) and many others satisfy an additional *intersection property*:

$$(7.5) \quad x \, A \, y \text{ and } x \, A \, z \text{ imply } x \, A \, (y \cap z).$$

We shall not generally assume (7.5) in this short discussion, but it is often convenient.

Each equivalence relation represents a *space*: the space of all its equivalence classes. Such spaces form a category more extensive than the category of retracts studied above. The familiar functors can be extended to this larger category by these definitions:

$$(7.6) \quad A \to B = \{\langle \lambda x.\, u(x), \lambda x.\, v(x) \rangle \mid u(x) \, B \, v(y) \text{ whenever } x \, A \, y\},$$

$$(7.7) \quad A \times B = \{\langle \langle x, x' \rangle, \langle y, y' \rangle \rangle \mid x \, A \, y \text{ and } x' \, B \, y'\},$$

$$(7.8) \quad A + B = \{\langle \langle 0, x \rangle, \langle 0, y \rangle \rangle \mid x \, A \, y\} \cup \{\langle \langle 1, x' \rangle, \langle 1, y' \rangle \rangle \mid x' \, B \, y'\}.$$
