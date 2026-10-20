# Information systems

Intuitively, an information system is a set of “propositions” that can be made about “possible elements” of the desired domain. We will assume that sufficiently many propositions have been supplied to distinguish between distinct elements; as a consequence, an element can be constructed abstractly as the set of all the propositions that are true of it. Partial elements have “small” sets; while total elements have “large” sets (even: maximal). To make this somewhat rough idea precise, we have to explain—by a suitable, but small choice of axioms—how the collection of all propositions relevant to the domain hangs together, or better, is structured as a set of abstract propositions. Fortunately, the axioms for this structure are very simple and familiar, which is a great help in making up examples.

**DEFINITION 2.1.** An *information system* is a structure

$$(D, \Delta, \mathrm{Con}, \vdash),$$

where $D$ is a set (the set of data objects or propositions), where $\Delta$ is a distinguished member of $D$ (the least informative member), where $\mathrm{Con}$ is a set of finite subsets of $D$ (the consistent sets of objects), and where $\vdash$ is a binary relation between members of $\mathrm{Con}$ and members of $D$ (the
entailment relation for objects). Concerning $\mathrm{Con}$, the following axioms must be satisfied for all finite subsets $u, v \subseteq D$:

(i) $u \in \mathrm{Con}$, whenever $u \subseteq v \in \mathrm{Con}$;

(ii) $\{X\} \in \mathrm{Con}$, whenever $X \in D$; and

(iii) $u \cup \{X\} \in \mathrm{Con}$, whenever $u \vdash X$.

Concerning $\vdash$, the following axioms must be satisfied for all $u, v \in \mathrm{Con}$, and all $X \in D$:

(iv) $u \vdash \Delta$;

(v) $u \vdash X$, whenever $X \in u$; and

(vi) if $v \vdash Y$ for all $Y \in u$ and $u \vdash X$, then $v \vdash X$.

In words we may say of $\mathrm{Con}$ that, as a set of sets, (i) it is closed under subsets, (ii) it contains all singletons, and (iii) adjunction of an entailed object to a consistent set preserves consistency. Concerning $\vdash$, which should be viewed as a “multiary” relation, we may say that (iv) $\Delta$ is entailed by anything, (v) $\vdash$ is reflexive, and (vi) $\vdash$ is transitive. (The last two properties are both expressed in a way appropriate to a multiary relation on members of $D$.) ■

The best advice is to think of the members of $D$ as consisting of finite data objects, some of which are more informative than others. The word “finite” should be taken here in the sense of “fully circumscribed”—as regards what is given in $\mathbf{A}$ these data objects can be comprehended in “one step.” It is of course possible to introduce information systems where the data objects are infinite sets, but relative to $\mathbf{A}$ they are finite as data objects.

The member that provides zero information is $\Delta$. Data objects are intended to give information about possible elements of the domain to be constructed, so if we were to use $\Delta$ alone, we would be describing the least defined element usually written as $\bot$.

Not just any combination of data objects will describe a possible element, however; hence, the need for the notion of consistency. If $u \in \mathrm{Con}$ is false, then the “propositions” in $u$ cannot all be applied to the same element at the same time. Finally we have to agree that, in general, the propositions to be allowed are rarely mutually independent. It follows that an entailment relation must be imposed to record the dependencies that do hold among the propositions. With these informal understandings, the axioms chosen should all be self-evident.

**A first example.** Suppose we let $D$ be the set of non-negative integers, where we think of an integer $n$ as an abbreviation of the proposition $n \le x$. Here $x$ is a yet-to-be-determined element, about which one proposition gives only a little information. We can identify $\Delta$ with $0$, and take $\mathrm{Con}$ to be the set of all finite subsets of $D$. The entailment relation can be defined formally in the way suggested by the intuitive reading of the data objects:

$$\{n_0, \dots, n_{k-1}\} \vdash m \quad\text{iff either } m = 0 \text{ or } m \le n_i \text{ for some } i < k.$$

(Remember to think of the same possible $x$ on both sides of the $\vdash$.) That $\vdash$ is an entailment relation in the sense of our axioms is clear. ■
**A second example.** The first example is possibly misleading because all (finite) sets of data objects were allowed to be consistent. The example can be modified in a natural way so this is not so; of course, quite a different system will be obtained. The idea is to let $D$ be the set of all pairs $(n, m)$ of integers with $n < m$, where such a pair stands now for the proposition $n < x < m$. Clearly the two data objects $(0, 2)$ and $(3, 7)$ taken together are inconsistent. (Why?)

Oh, I see, I have left out $\Delta$ from $D$; we must therefore include the somewhat artificial pair $(0, \infty)$ with the obvious interpretation. When I say “obvious interpretation” here I mean that $u \in \mathrm{Con}$ can be defined by saying that there must be an integer satisfying all the “propositions” in $u$. Further, $u \vdash X$ can be defined by saying that whenever an integer satisfies all the propositions in $u$, then it must satisfy $X$. The notion of “satisfy” really should be obvious from the intuitive reading given to the data objects, and the reader can verify easily that all the axioms hold for this example of an information system. ■

**A third example.** Let $A$ and $B$ be two fixed sets, and let $D$ as a set consist of the ordered pairs $(a, b)$, with $a \in A$ and $b \in B$, plus the extra object $\Delta$. Here the “information” contained in $(a, b)$ is that $a$ is mapped to $b$ by a yet-to-be-determined function. With this thought in mind, we will know that a finite set of data objects is consistent just in case it is possible that they can all belong to the same function. Formally, we can assert:

$$\{(a_0, b_0), \dots, (a_{k-1}, b_{k-1})\} \in \mathrm{Con} \text{ iff for all } i, j < k \text{ whenever } a_i = a_j, \text{ then } b_i = b_j.$$

It is something of a bother having to throw in $\Delta$ in this case, but all we have to say is that if $u$ is consistent under the above rule, then so also will $u \cup \{\Delta\}$; and these are the only consistent sets of data objects for this example. Perhaps it would make more sense to use $\{(a, b)\}$ in place of the simpler $(a, b)$, and then we could set $\Delta = \emptyset$ more naturally. From this point of view we can regard each data object as a (very small!) fragment of the graph of a function; the consistent sets then point to larger fragments of graphs.

The definition of the entailment relation is the minimal one:

$$u \vdash X \text{ iff either } X = \Delta \text{ or } X \in u.$$

These examples show that sometimes the main part of the structure is in $\mathrm{Con}$, sometimes it is in $\vdash$, and sometimes it is in the interplay between the two notions. The object $\Delta$ is not in itself very important, but it is sometimes useful to have an object there that can always be counted upon to act in the same way in every system. ■

Already in formulating the axiom about the transitivity of $\vdash$ a relation between sets in $\mathrm{Con}$ was suggested; we now make this official.

**DEFINITION 2.2.** *For $u, v \in \mathrm{Con}$ we write $u \vdash v$ to mean that $u \vdash X$ for all $X \in v$.* ■

**PROPOSITION 2.3.** *For all $u, v, w, u', v' \in \mathrm{Con}$, we have:*

(i) $\emptyset \vdash \{\Delta\}$;

(ii) $u \vdash v$ implies $u \cup v \in \mathrm{Con}$;

(iii) $u \vdash u$;
(iv) $u \vdash v$ and $v \vdash w$ imply $u \vdash w$;

(v) $u' \supseteq u$, $u \vdash v$, and $v \supseteq v'$ imply $u' \vdash v'$; and

(vi) $u \vdash v$ and $u \vdash v'$ imply $u \vdash v \cup v'$.

Proof. Obvious. ■

*Remark.* It is not worth formulating a formal result at this point, but it should be clear that the properties in 2.3 could have been used as axioms. That is to say, we could have taken $\vdash$ as a binary relation on the set $\mathrm{Con}$, used 2.1 (i)–(ii) and 2.3 (i)–(vi) as axioms. (Actually, 2.3(ii) is redundant.) The old-style entailment relation would then be definable by:

$$
u \vdash X \quad \text{iff} \quad u \vdash \{X\}.
$$

The previous axioms in 2.1 are then easily proved from the new ones. ■

*Some notation.* As it is not always clear what structure is meant if we refer to a domain simply by naming its underlying set of data objects, it will be better if we use a letter to refer to an information system as a whole. We shall therefore write:

$$
\mathbf{A} = (D_{\mathbf{A}}, \Delta_{\mathbf{A}}, \mathrm{Con}_{\mathbf{A}}, \vdash_{\mathbf{A}}),
$$

and say that $\mathbf{A}$ is an information system—with its parts as indicated. For a more informal discussion, the notation without subscripts can suffice, but there can be problems when several different systems are involved. ■

So much for the definition of what a system is as a mathematical structure. The next question is: What is it good for? More precisely, if information systems are the backbones of domains, then where are the elements? That is the topic of the next section.
