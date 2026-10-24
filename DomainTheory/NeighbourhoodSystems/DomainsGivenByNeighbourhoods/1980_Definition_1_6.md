# Definition 1.6

## Human-English

DEFINITION 1.6. The (ideal) elements of a neighbourhood system $\mathcal{D}$ are those subfamilies $x \subseteq \mathcal{D}$ where:

(i) $\Delta \in x$;

(ii) $X, Y \in x$ always implies $X \cap Y \in x$; and

(iii) whenever $X \in x$ and $X \subseteq Y \in \mathcal{D}$, then $Y \in x$.

The *domain* of all such elements is written as $|\mathcal{D}|$. $\square$

<!-- page 13 -->

The idea of 1.6 is a well-known mathematical device: the families $x$ satisfying (i)–(iii) are usually called *filters*. Most frequently the emphasis is put on the *maximal* filters, and these would be our *total* elements; however, in general, the proof that maximal filters exist is non-constructive, so for our purposes it is better not to neglect the partial filters. When maximal filters can be found, well and good, but we do not have to insist on them. Note that the generality of 1.6 is achieved by not requiring that there is a sequence of neighbourhoods that "generates" the filter $x$. (See Exercise 1.22.)

We have often said that neighbourhoods determine partial elements by themselves; we now make this remark precise.

## AI: Human-English to AI-Lean

**[Element.lean](Element.lean)**

@import "Element.lean"
