# Approximable mappings between domains

Once a general notion of set or domain has been defined mathematically, the next major issue is: How are the different domains to be related one to another? The answer to this important question can many times be given by defining an appropriate concept of mapping between domains. The answer need not be unique; the same collection of domains may support more than one idea of function depending on the special aspects of the domains that need to be brought out. In the case of the kinds of domains being studied here, there are two principal answers, one of which is to be explained in this section.

In order to understand an appropriate notion of a mapping or a function between domains constructed from information systems, we have to refer back to the way in which elements are introduced. As we have seen in Section 3, an element is a consistent, closed set of data objects. To generate an element, one has to generate more and more of the finite consistent subsets of the element. Note that the separate data objects have to be grouped into these finite consistent sets, because the entailment relation may require a finite set of arbitrary size on the left in making the necessary entailments for closure. It is this kind of passage from a finite set to its closure that is to be generalized in defining mappings.

Consider two domains. To map from one to another, some information about a possible element of the first is presented as input to the function $f$. Then as output the function $f$ starts generating an element. If the input were $u$, a consistent set of the first domain, then part of the output in the second domain might be a consistent set $v$. We could say that there is an input/output relationship set up by $f$, and indicate by $u\ f\ v$ that this relation holds going from $u$ in the first domain to $v$ in the second. Of course to get the full effect of $f$, it is necessary to take all the $v$'s related to a given $u$, because even a small finite amount of input may cause an infinite amount of output. But every element of a domain is just the sum total of its finite subsets (finite approximations), so it is sufficient to make the mapping relationship go between finite sets. Here is the formal definition with the exact conditions that the relation $f$ must satisfy.

**DEFINITION 5.1.** Let $\mathbf{A}$ and $\mathbf{B}$ be two given information systems. An *approximable mapping* $f : \mathbf{A} \to \mathbf{B}$ is a binary relation between the two sets $\mathrm{Con}_{\mathbf{A}}$ and $\mathrm{Con}_{\mathbf{B}}$ such that:

(i) $\emptyset\ f\ \emptyset$;

(ii) $u\ f\ v$ and $u\ f\ v'$ always imply $u\ f\ (v \cup v')$; and

(iii) $u' \vdash_{\mathbf{A}} u$, $u\ f\ v$, and $v \vdash_{\mathbf{B}} v'$ always imply $u'\ f\ v'$.
We say that $\mathbf{A}$ is the *source* of $f$ and $\mathbf{B}$ is the *target*. $\blacksquare$

Intuitively the relationship $u\ f\ v$ is an input/output passage which can be read informally as: “if you are willing to give at least $u$ amount of information about the argument, then the mapping $f$ is willing to give at least $v$ amount of information about the value (and possibly even more—if you are patient).” Condition (i) means that no (non-trivial) information about the input merits no information about the output. Condition (ii) implies that all the contributions to the output from a fixed input are consistent, and in fact the union of two of the output sets is again an output set. Output corresponding to a fixed input is cumulative. Condition (iii) assures us that the mapping relation $f$ works in harmony with the two entailment relations: if a certain relationship holds, and if the left-hand side is strengthened while the right-hand side is weakened, then the mapping relation must continue to hold. What we must discuss next is what this means for elements.

Before defining the notion of function value, however, it is useful to remark that in the definition of approximable mapping the form of the statement could be simplified by reducing sets on the right to their elements. Specifically, we note the equivalence:

$$u\ f\ v \text{ iff } u\ f\ \{Y\} \text{ for all } Y \in v.$$

In other words an approximable mapping is completely determined by the relation set up between consistent sets on the left and single data objects on the right.

**DEFINITION 5.2.** If $f : \mathbf{A} \to \mathbf{B}$ is an approximable mapping between information systems, and if $x \in |\mathbf{A}|$ is an element of the first, then we define the *image* (or *function value*) of $x$ under $f$ by the formula:

$$f(x) = \{Y \in D_{\mathbf{B}} \mid u\ f\ \{Y\} \text{ for some } u \subseteq x\}.$$

Alternatively, we could use the equivalent formula:

$$f(x) = \bigcup \{v \in \mathrm{Con}_{\mathbf{B}} \mid u\ f\ v \text{ for some } u \subseteq x\}.\ \blacksquare$$

Note that, under Definition 5.2, it has to be *proved* that the image of an element in $|\mathbf{A}|$ lies in $|\mathbf{B}|$ in order to justify the use of the ordinary function-value notation. But both the consistency and the closure under entailment of $f(x)$ are direct consequences of the properties in the definition of approximable mapping.

**PROPOSITION 5.3.** *Let $f, g : \mathbf{A} \to \mathbf{B}$ be two approximable mappings between two information systems. Then*

*(i) $f$ always maps elements to elements under Definition 5.2;*

*(ii) $f = g$ iff $f(x) = g(x)$ for all $x \in |\mathbf{A}|$; and*

*(iii) $f \subseteq g$ iff $f(x) \subseteq g(x)$ for all $x \in |\mathbf{A}|$.*

Moreover, the approximable mappings are monotone in the sense that

(iv) $x \subseteq y$ in $|\mathbf{A}|$ always implies $f(x) \subseteq f(y)$ in $|\mathbf{B}|$.

*All these results follow from the observation that*
(v) $\quad u\ f\ v \text{ iff } \bar{v} \subseteq f(\bar{u}),$

for all $u \in \mathrm{Con}_{\mathbf{A}}$ and all $v \in \mathrm{Con}_{\mathbf{B}}$. $\blacksquare$

The proof is straightforward, and it completely justifies the use of the function-value notation. Consequently, the question arises as to whether the characterization of approximable mappings could not have been given in terms of elements in the first place. The answer is yes. Indeed, approximable mappings correspond exactly to functions on elements preserving unions of chains (this, in the case of countable information systems; directed unions must be used in general). This characterization has also been called “continuity,” because it is equivalent to saying that the mappings between elements are continuous mappings in the topological sense, when $|\mathbf{A}|$ and $|\mathbf{B}|$ are regarded as topological spaces, as explained in the last section. The reason for the word “approximable” is explained in Section 7.

Having justified the idea of an approximable mapping as a transformation on elements, the next step is to combine mappings. It is hardly surprising to learn that compositions of approximable mappings are approximable, which in mathematical terms means that the domains together with the approximable mappings form a *category*. The interesting part starts when we want to combine *domains*. But, to fix ideas, it is useful to spell out how compositions take place on the level of the data objects and consistent sets. For instance, it was noted that in any information system $\vdash$ is transitive on $\mathrm{Con}$, and in Definition 5.1 a transitivity condition comes in. There is a perfectly good reason for the parallelism, for, as we see next, the first idea (entailment) is a special case of the second (approximable mapping).

**PROPOSITION 5.4.** *Let $\mathbf{A}$ be an information system. Then the following formula defines an approximable mapping $I_{\mathbf{A}} : \mathbf{A} \to \mathbf{A}$:*

(i) $\quad u\ I_{\mathbf{A}}\ v \text{ iff } u \vdash_{\mathbf{A}} v,$

*for all $u, v \in \mathrm{Con}_{\mathbf{A}}$. And we have:*

(ii) $\quad I_{\mathbf{A}}(x) = x,$

*for all $x \in |\mathbf{A}|$.* $\blacksquare$

In other words, the given entailment relation itself defines the identity function on the domain in question; and of course, the identity function is an approximable mapping.

**PROPOSITION 5.5.** *Let $f : \mathbf{A} \to \mathbf{B}$ and $g : \mathbf{B} \to \mathbf{C}$ be two approximable mappings. Then the following formula defines an approximable mapping $g \circ f : \mathbf{A} \to \mathbf{C}$:*

(i) $\quad u\ (g \circ f)\ w \text{ iff } u\ f\ v \text{ and } v\ g\ w \text{ for some } v \in \mathrm{Con}_{\mathbf{B}},$

*for all $u \in \mathrm{Con}_{\mathbf{A}}$ and $w \in \mathrm{Con}_{\mathbf{C}}$. And we have:*

(ii) $\quad (g \circ f)(x) = g(f(x)),$

*for all $x \in |\mathbf{A}|$.* $\blacksquare$

In other words, composition of input/output relations is effected by putting the input into the first, getting some output, and then putting that in as input to the second. The correctness of this
recipe on elements (i.e. formula 5.5(ii)) follows from the basic formula 5.3(v). Because the class of all sets and arbitrary mappings forms a category—in the formal meaning of the word—the above three propositions show that the totality of information systems and approximable mappings also forms a category: a sub-category of the category of sets. We have given a special representation to the category by our use of data objects and consistent sets, and we have thereby put the elements into a secondary position—for a good reason. But the elements are there to use. The axioms for a category could also be verified directly using the basic definitions like 5.4(i) and 5.5(i); the details are bland. The more interesting topic is: what are the closure conditions on our domains; how do we construct new domains given old ones?

Before we go on to the first basic constructs of sums and products of domains, we remark on some other easy examples of approximable mappings: constant maps.

**PROPOSITION 5.6.** *Given information systems $\mathbf{A}$, $\mathbf{B}$, $\mathbf{C}$, and $\mathbf{D}$, and given a fixed element $b \in |\mathbf{B}|$, then there is a unique approximable mapping $\mathrm{const}\ b : \mathbf{A} \to \mathbf{B}$ such that:*

(i) $\quad (\mathrm{const}\ b)(x) = b,$

*for all $x \in |\mathbf{A}|$. Moreover, we have:*

(ii) $\quad f \circ (\mathrm{const}\ b) = \mathrm{const}\ f(b),$

*for all approximable mappings $f : \mathbf{B} \to \mathbf{C}$; and*

(iii) $\quad (\mathrm{const}\ b) \circ g = \mathrm{const}\ b,$

*for all approximable mappings $g : \mathbf{D} \to \mathbf{A}$.* $\blacksquare$

The proof is immediate, since we need only interpret the input/output relation $u\ (\mathrm{const}\ b)\ v$ as meaning $v \subseteq b$. We note that our notation is somewhat ambiguous since, for example, in 5.6(iii) we are using $\mathrm{const}\ b$ in two senses: once as a mapping from $\mathbf{A}$, and once as a mapping from $\mathbf{D}$. In fact, we should hang two subscripts on the thing to fix both the source and the target of the mapping. This is too painful, however, and we generally rely on context to make the meaning clear. (Formal rules of type checking can be given, so on a computer-based system all the necessary subscripts could be put back in. Thus, the kind of ambiguity we are dealing with here is not very serious.)
