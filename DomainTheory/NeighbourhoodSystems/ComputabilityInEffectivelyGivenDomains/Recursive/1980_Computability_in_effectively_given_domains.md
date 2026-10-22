# Computability in effectively given domains

For the domain $N$ the strict functions from $N$ into $N$, the strict maps $f : N \to N$, correspond exactly to the partial functions $g : N \to N$ (as we wrote in 5.6 we had $f = \bar{g}$). For such functions there is a standard theory of computability: $g$ is called computable if it can be defined as a partial recursive function with its "program" written down in a certain standard form. The non-strict maps $h : N \to N$ are all constant, and so are intuitively computable; so we know all about computable maps in $|N \to N|$ in general. The question is: what are the computable maps on (elements of) other domains?

The answer will of course depend on how the domain is presented to us. Even with $N$, there are continuum many isomorphisms $\pi : N \to N$ of $N$ onto itself, not all of which can be computable. That is, if we permute $N$ and, so to speak, present the integers in a different order, then a well-behaved computable function $f : N \to N$ may well be transformed into a non-computable function,

$$
\pi \circ f \circ \pi^{-1} : N \to N.
$$

(Hint: Consider the characteristic function $e$ of the even numbers. Take $f = \bar{e}$ and let $\pi$ be very horrid.) The reason we imagined we knew which were the computable $f : N \to N$ is that $N$ is always thought of in a standard presentation. We must thus define "in general" a concept of an *effectively given domain*, that is to say, one with a sufficiently computable presentation to represent the additional knowledge about the domain.

The main idea will be that the *finite elements* of $|D|$ should be regarded as the ones initially known. Abstractly, to know a finite element is to know how it is *related* to other finite elements.
Of course, this will mean that we will allow at most a countable infinity of finite elements — but this restriction well accords with intuition. To make precise the terminology "related to" it proves most convenient to go back to the neighbourhoods (in any case they are in a one-one correspondence with the finite elements).

- [Definition 7.1](../Definition71/1980_Definition_7_1.md)
- [Definition 7.2](../Definition72/1980_Definition_7_2.md)
- [Proposition 7.3](1980_Proposition_7_3.md)
- [Theorem 7.4](../Theorem74/1980_Theorem_7_4.md)
- [Theorem 7.5](../Theorem75/1980_Theorem_7_5.md)
- [Theorem 7.6](../Theorem76/1980_Theorem_7_6.md)
- [Proposition 7.7](../Proposition77/1980_Proposition_7_7.md)
- [Example 7.8](../Example78/1980_Example_7_8.md)
- [Definition 7.9](../Definition79/1980_Definition_7_9.md)
- [Proposition 7.10](../Proposition710/1980_Proposition_7_10.md)
- [Definition 7.11](../Definition711/1980_Definition_7_11.md)
- [Proposition 7.12](../Proposition712/1980_Proposition_7_12.md)
- [Exercise 7.13](../Exercise713/1980_Exercise_7_13.md)
- [Exercise 7.14](../Exercise714/1980_Exercise_7_14.md)
- [Exercise 7.15](../Exercise715/1980_Exercise_7_15.md)
- [Exercise 7.16](../Exercise716/1980_Exercise_7_16.md)
- [Exercise 7.17](../Exercise717Part2/1980_Exercise_7_17.md)
- [Exercise 7.18](../1980_Exercise_7_18.md)
- [Exercise 7.19](../Exercise719/1980_Exercise_7_19.md)
- [Exercise 7.20](../Exercise720/1980_Exercise_7_20.md)
- [Exercise 7.21](../Exercise721/1980_Exercise_7_21.md)
- [Exercise 7.22](../1980_Exercise_7_22.md)
- [Exercise 7.23](../Exercise723/1980_Exercise_7_23.md)
- [Exercise 7.24](../Exercise724/1980_Exercise_7_24.md)
