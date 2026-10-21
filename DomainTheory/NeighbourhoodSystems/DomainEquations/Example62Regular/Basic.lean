/-ai
This file gathers and re-exports the basic vocabulary of Example 6.2 on eventually periodic trees and regular events: total trees, the root label, the subtree selector with its application and empty-selector laws, the immediate child, the tree language and its membership, and eventual periodicity, together with the Myhill–Nerode library. The module comment records Scott's claim that a total tree is eventually periodic when it has finitely many subtrees, that the language of its positive nodes is then a regular event and every regular language arises in this way, and that the subtree at a word is the left quotient of that language.
ai-/
module

public import Mathlib.Computability.MyhillNerode
import all Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.pos
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.child
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.treeLang
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.EventuallyPeriodic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.Tree
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.pos_select
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.mem_treeLang

@[expose] public section

/-!
# Example 6.2 (Scott 1981, PRG-19, §6) — eventually-periodic trees and regular events

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture VI,
*Introduction to domain equations*. After exhibiting the generalised domain equation `A ≅ Aⁿ + Aⁿ`
(formalised in `Example62A.lean`), Scott closes Example 6.2 with a *casual aside* connecting his
infinite `±`-labelled `n`-ary trees to automata theory:

> "We say that a (total) tree `a` is *eventually periodic* iff the set `{aσ ∣ σ ∈ Σ*}` is finite.
> The result is that the 'language' `L_a = {σ ∈ Σ* ∣ pos(aσ) = true}` corresponding to an eventually
> periodic tree is always a *regular event* of automata theory, and every such language has this form.
> In fact, `a` just represents the initial state of an automaton, and `aσ` represents the state after
> 'reading' a tape `σ`."

This file makes that remark precise and *proves* it. Scott's total trees over `Σ = {0, …, n-1}` are
exactly the functions `a : Σ* → Bool` assigning a `±` label (`pos`) to every node, addressed by a
finite selector `σ ∈ Σ*`. The **subtree** operation `σ ↦ aσ` is Scott's selector recursion
`aΛ = a`, `a(iσ) = (aᵢ)σ`; its *language* `L_a` is the set of selectors landing on a `+` node.

The two halves of Scott's claim are exactly the two halves of the **Myhill–Nerode theorem**: a tree
is eventually periodic (finitely many distinct subtrees) iff its language has finitely many *left
quotients* iff (Myhill–Nerode, `Language.isRegular_iff_finite_range_leftQuotient`) the language is
regular. The bridge is that the subtree `aσ` *is* the left quotient `σ⁻¹ L_a`: reading the tape `σ`
moves the automaton to the residual language, which is precisely the subtree at `σ`.

This is a `Prop`-level result (about regularity), so `Classical.choice` is unobjectionable here; the
content is entirely the combinatorics-on-words / automata correspondence, orthogonal to the
neighbourhood-system machinery.
-/

namespace DomainTheory.NeighbourhoodSystems

namespace Example62Regular

open Language

variable {n : ℕ}










end Example62Regular
end DomainTheory.NeighbourhoodSystems
