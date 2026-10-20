/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGetStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.rtbl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gList
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.le_pair_left
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.unpair_fst_le
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.nat_shape
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.pair_lt_succ_sq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.max_sq_le_pair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.pair_lt_pair_of_lt
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_succ
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_odd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_even
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_surj
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_zero_inter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_inter_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_odd_inter_odd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_odd_inter_even
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_even_inter_odd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_even_inter_even
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.memS_sub_embZero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.memS_sub_embPair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.exists_sub_embZero_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.exists_sub_embPair_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_eq_Gamma_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGetStp_pair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet_foldl_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet_foldl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet_encodeList
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.primrec_listGet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gOf_def
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.rtbl_eq_encode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.getD_gList
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet_rtbl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.rtbl_eq_rec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.primrec_rtbl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.primrec_gOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.primrec_listGet₂
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_i0
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_j0
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_ll
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_ln
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_nl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_nn
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.primrec_dsharpStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharp_decider_spec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharp_intI_correct
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharp_interEq_iff

@[expose] public section

/-!
# Proposition 7.7 (Scott 1981, PRG-19, §7) — `D^§` is effectively given

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Proposition 7.7.** For any effectively given domain `D`, the domain `D^§` is also effectively
> given, and all the combinators of Example 6.1 prove to be computable.

Scott transposes everything back to `ℕ` and gives the enumeration of `D^§` (Example 6.1's tree
algebra, `Example61.Dsharp`) by a course-of-values recursion. In our model `D^§` lives over
`List Bool × α` (Example 6.1), so the enumeration is `V : ℕ → Set (List Bool × α)`:

* `V 0 = Γ`                  (the master neighbourhood of `D^§`);
* `V (2n+1) = 0·Xₙ`          (`embZero` of the `n`-th `D`-neighbourhood `Xₙ = P.X n`);
* `V (2n+2) = 1·V_{p n} ∪ 2·V_{q n}` (`embPair` of two earlier neighbourhoods).

Here `p n = n.unpair.1` and `q n = n.unpair.2` are Scott's `p, q` (inverse pairing): both are `≤ n`,
hence the subscripts `p n, q n` of `V_{2n+2}` are `< 2n+2`, so the recursion is well-founded and
membership stays recursive — exactly Scott's observation.

This file builds the construction in milestones:

* **Foundational layer (this commit):** `Vsharp` and its core math — `mem_X` (each `V k ∈ 𝒟^§`),
  `surj` (every `𝒟^§`-neighbourhood is some `V k`), nonemptiness. All choice-free.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

/-! ### A left bound for `Nat.unpair` (local, to keep `Recursive.lean`'s cache warm). -/




/-! ### `Nat.pair` is strictly monotone on strict componentwise order.

Needed so the node∩node recursive child code `pair (a.1) (b.1)` is `< pair (2a+2) (2b+2)`, hence
present in the memo table. Proof via `max² ≤ pair _ _ < (max+1)²`. -/




/-! ### The enumeration `V : ℕ → 𝒫(List Bool × α)`. -/


variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)





/-! ### `mem_X`, `surj`, nonemptiness. -/




/-! ### Per-parity intersection identities.

These are the choice-free heart of Scott's "the reader has to check that 7.1(i)–(ii) hold for the
`Vₖ`. The idea is that any such check is either (1) trivial, or (2) something already assumed about
`D` and the `Xₙ`, or (3) can be thrown back to some sets `Vₘ` with strictly smaller subscripts."

* `V₀ = Γ` is the identity for `∩` (cases (1));
* odd ∩ odd reduces to `D`'s own intersection `Xₐ ∩ X_b` (case (2));
* odd ∩ even (and even ∩ odd) are `∅` — inconsistent (case (1), and `∅ ∉ 𝒟^§`);
* even ∩ even is `embPair` of the *component* intersections, whose subscripts `unpair.1 / unpair.2`
  are strictly smaller (case (3)). -/







/-! ### `MemS`-subset inversions and the consistency-via-subset equivalences.

A nonempty `D^§`-neighbourhood contained in `embZero Y` must itself be an `embZero` (its tokens have
empty `{1,2}`-path); contained in `embPair A B`, an `embPair`. These give the bridge between Scott's
consistency relation on `D^§` (`∃ l, V_l ⊆ V_n ∩ V_m`) and the recursive sub-checks: `embZero`
consistency reduces to `D`'s, and `embPair` consistency to the two components'. -/






/-! ### A primitive-recursive course-of-values memo evaluator.

The `D^§` deciders (`cons`, `inter`, equality) recurse on the index *trees*: e.g.
`inter(2a+2, 2b+2)` recurses on `inter(a.1, b.1)` and `inter(a.2, b.2)`. The combined measure
`w = Nat.pair n m` strictly decreases on every recursive call, so each decider is a **unary
course-of-values recursion** on `w`. We realise course-of-values by a primitive-recursive *memo
table*: `rtbl step w` codes the reverse list `[g(w-1), …, g 0]` (`g v = step (pair v (table for v))`),
built by a single `Nat.Primrec.prec` whose step is a cons. To read `g v` for `v < w` inside `step`,
we look up position `w-1-v` of the reverse table via `listGet`. All choice-free. -/



















/-! ### The combined `D^§` decider step (`eq`/`cons`/`inter` triple).

All three `D^§` deciders recurse the same way on `(i, j)`, so we compute them together as a packed
triple `packT eqBit consBit interIdx`. The step `dsharpStep fcons feq finter` is fed Scott's three
`D`-level primitive-recursive functions: `fcons`/`feq` are the extracted `{0,1}` characteristic
functions of `P.cons_computable`/`P.eq_computable`, and `finter` is `P.inter` (on `Nat.pair` codes).
The combined index is `w = Nat.pair i j`; in the node∩node case the children's results are read from
the memo table by `listGet`. -/




variable (fcons feq finter : ℕ → ℕ)









/-! ### Correctness of the decider step (strong induction on the combined code).

Given that `fcons`/`feq`/`finter` correctly decide `D`-consistency / `D`-equality / `D`-intersection,
the packed triple `gOf (dsharpStep …)` correctly decides `D^§`-consistency, computes the
`D^§`-intersection index, and decides `D^§`-equality. Proved together by strong induction on the
combined code `Nat.pair i j`; the node∩node case recurses to strictly smaller codes (present in the
memo table by `pair_lt_pair_of_lt`). -/




/-! ### Proposition 7.7: `D^§` is effectively given.

Assembling the pieces into a `ComputablePresentation (Dsharp D hD)`. The enumeration is `Vsharp`;
relation 7.1(ii) (consistency) and 7.1(i) (intersection-equality) are decided by the packed-triple
deciders; the primitive-recursive intersection function reads the `intI` component (built with dummy
`eq`/`cons` bits, which it does not depend on). Choice-free: the `Prop` fields obtain `D`'s
existential deciders, the data fields use only `P.inter` (data). -/

end Proposition77
end DomainTheory.NeighbourhoodSystems
