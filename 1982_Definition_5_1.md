# Definition 5.1

**DEFINITION 5.1.** Let $\mathbf{A}$ and $\mathbf{B}$ be two given information systems. An *approximable mapping* $f : \mathbf{A} \to \mathbf{B}$ is a binary relation between the two sets $\mathrm{Con}_{\mathbf{A}}$ and $\mathrm{Con}_{\mathbf{B}}$ such that:

(i) $\emptyset\ f\ \emptyset$;

(ii) $u\ f\ v$ and $u\ f\ v'$ always imply $u\ f\ (v \cup v')$; and

(iii) $u' \vdash_{\mathbf{A}} u$, $u\ f\ v$, and $v \vdash_{\mathbf{B}} v'$ always imply $u'\ f\ v'$.
We say that $\mathbf{A}$ is the *source* of $f$ and $\mathbf{B}$ is the *target*. $\blacksquare$

Intuitively the relationship $u\ f\ v$ is an input/output passage which can be read informally as: “if you are willing to give at least $u$ amount of information about the argument, then the mapping $f$ is willing to give at least $v$ amount of information about the value (and possibly even more—if you are patient).” Condition (i) means that no (non-trivial) information about the input merits no information about the output. Condition (ii) implies that all the contributions to the output from a fixed input are consistent, and in fact the union of two of the output sets is again an output set. Output corresponding to a fixed input is cumulative. Condition (iii) assures us that the mapping relation $f$ works in harmony with the two entailment relations: if a certain relationship holds, and if the left-hand side is strengthened while the right-hand side is weakened, then the mapping relation must continue to hold. What we must discuss next is what this means for elements.

Before defining the notion of function value, however, it is useful to remark that in the definition of approximable mapping the form of the statement could be simplified by reducing sets on the right to their elements. Specifically, we note the equivalence:

$$u\ f\ v \text{ iff } u\ f\ \{Y\} \text{ for all } Y \in v.$$

In other words an approximable mapping is completely determined by the relation set up between consistent sets on the left and single data objects on the right.
