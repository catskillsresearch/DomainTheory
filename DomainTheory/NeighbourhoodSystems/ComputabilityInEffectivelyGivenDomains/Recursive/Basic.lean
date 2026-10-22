/-ai
This file proves the choice-free recursion theory for Scott's Lecture VII. A predicate is recursively decidable when it has a primitive-recursive characteristic function, and recursively enumerable when it is the projection of a recursively decidable relation. The arguments use the primitive-recursive constructors, the choice-free pairing round-trip, and arithmetic discharged by omega.

Identity is the pairing of the two projections, rewritten by the round-trip. Addition, multiplication, predecessor, and truncated subtraction are primitive recursions whose recursors compute the operations by induction or by cases, and the pointwise sum, product, difference, and selection are those operations composed through pairing. A product of naturals is one exactly when both factors are one, by divisibility. Recursive decidability transfers across a pointwise equivalence by reusing the characteristic function, reindexes by composition, and is closed under conjunction by multiplying the deciders. Equality of two primitive-recursive functions has characteristic one minus the sum of the two truncated differences. Negation uses the same truncated-subtraction characteristic. Excluded middle is the case split on whether the decider returns one, and disjunction rewrites through De Morgan using that split. Every recursively decidable predicate is recursively enumerable by reading the decider on the second component of the pair and taking witness zero. Recursive enumerability transfers across equivalence, reindexes by pairing the search variable with the image, is closed under conjunction by pairing the two search variables, under existential projection by folding the new variable into the search code, and under disjunction by tagging the witness with zero or one.

The first component of a pair is at most the pair, by unfolding the pairing function. The length of a list is at most its code, by induction using that the tail code is at most the paired code. A fold step fixes the state on remaining code zero and, on a nonempty code, pops the head and applies the step. A counter-independent natural recursion is function iteration. After at least as many iterations as the length, the accumulator equals the list fold, by induction on the iteration count. Folding the code of a list is therefore that list fold, and folding an arbitrary code is the fold of its decoded list, because encoding after decoding is the identity by strong induction on the zero and successor equations of decoding, and decoding after encoding is the identity by induction on the list. The packed fold step and the fold of primitive-recursive inputs are primitive recursive by composition and one primitive recursion, rewritten to the iteration form.

The one-test and zero-test are at most one and primitive recursive by truncated subtraction, and the zero-test equals one exactly at zero. The bounded-forall indicator is at most one and equals one exactly when every paired value in range is one, by induction on the bound and case analysis of the selection. The bounded-exists indicator is at most one, depends on the function only on the search range, and equals one exactly when some paired value in range is one, by the same induction. Both indicators, including the variant that threads an external parameter, are primitive recursive by a primitive recursion whose step selects the one-test. The re-forall step agrees with the accumulator function by unfolding, the character is the second component of the list fold of that function, and that fold is one exactly when the start flag is one and each witness entry satisfies the decidable body, by induction that splits the head off the coded witness list. The step and character are primitive recursive by the fold engine. Bounded universal quantification of a recursively enumerable predicate over a coded list is recursively enumerable: the forward direction builds a witness list by induction and encodes it, and the reverse direction reads the witness at the index supplied by membership.

The low bit of a bitwise or depends only on the two residues modulo two, by the test-bit law at position zero and a case split. One or step peels those low bits. After k iterations the running arguments, the weight, and the accumulator satisfy the division and weighted-or invariant, by induction on k. Iterating one more than the sum of the arguments therefore computes the or, because both arguments have been divided down to zero.

The list-and step is the selection of the decider, the character equals the corresponding list fold, and that fold is one exactly when the accumulator starts at one and every entry passes, by induction on the list. The character is therefore one exactly on membership in the decoded list, is at most one by the same fold, and the step is primitive recursive. A number is a binary digit exactly when its digit characteristic is one, by matching zero, one, and the remaining successor, so the all-binary-digits flag is one exactly when every decoded entry is zero or one, is at most one, and is primitive recursive by the fold.

Indexing returns the defaulted entry: the step increments a counter and captures the element when the counter meets the index, and the fold computes that conditional by induction. Tabulation after K steps decodes to the mapped range of the last K indices, so the full table decodes to the mapped initial range. In-range defaulted lookup is the element and out-of-range lookup is the default, by induction on the list, and lookup in a mapped range is the function value. The tabulation step and the table code are primitive recursive by composition and primitive recursion. Four-way tag dispatch is primitive recursive by nested selections of the one-test.

The fuel-ok body matches tags zero through three, by simplifying each selection, and is primitive recursive when the previous fuel function is. It depends on that function only at the two unpair projections, which are at most the code. List length is the fold of a successor counter, which equals the length by an auxiliary induction, and the step and character are primitive recursive. The numeric equality character is at most one and primitive recursive by truncated subtraction. The list-equality fold is one with a zero remainder exactly when the flag started at one and the list equals the decoded remainder, by induction, using that a zero remainder collapses the flag. Hence the equality character is one exactly when the two codes decode equally, it is at most one, and it is primitive recursive by the fold and the bit product.

Two lists with equal defaulted entries are equal, by comparing lengths through two distinct defaults and then comparing elements. Defaulted lookup of a take is lookup of the source in range, and lookup of a drop shifts the index, by induction on the drop count. The append tabulation reads the first code below the cut and the second code past it. Take and drop of a code decode to take and drop of the decoded list, by comparing defaulted entries with the tabulated lookup. Encoding a take or a drop does not increase the code, by induction and monotonicity of pairing, so those codes are at most the original code. Minimum and the take and drop codes are primitive recursive by selection, indexing, and tabulation.

The state-card body matches tags zero through three. When the fuel is at least the expression depth, the fuel-bounded state card of the Gödel code equals the state card, by induction on the expression, using the length of the encoded Boolean list in the single case. The body is primitive recursive when the previous function is, and it depends on that function only at the two unpair projections. The matches body matches the four tags, with a bounded search on concatenation and a bit product on intersection. When the fuel meets the depth, its character is one exactly when the Boolean matcher accepts: the unit and the single word are direct, concatenation searches a cut and uses take and drop of the encoded word, and intersection multiplies the recursive calls. The body is primitive recursive by multiplication, bounded search, and tag selection, the character is at most one by induction on fuel, and the body depends on the previous function only at codes at most the packed input, using that take and drop codes do not increase.

Every binary-digit code of length at most n lies strictly below the code bound, by induction on n and monotonicity of pairing, so a short encoded Boolean word lies below the bound, and encoding the decoding of an all-binary code recovers the code. When the fuel meets the depth, the nonempty decider is one exactly when the denoted language is nonempty, transporting a witness code to an accepted word and a short accepted word to a code below the bound. The cap code is the Gödel code of a cap. The subset guard is at most one. When the fuel meets both depths, the subset character is one exactly when the first language is contained in the second: the numeric bound equals the product of the powerset cardinalities by the state-card agreement, and the bounded-forall characteristic is compared with the Boolean subset test by transporting words across the Boolean encoding.
ai-/
module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.RecDecidable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.RecDecidable₂
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.RecDecidable₃
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.REPred
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.REPred₂
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.encodeList
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.foldStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.foldCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.decodeList
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.halfParity
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.isOne
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.isZero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.bForallFn
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.bExistsFn
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.reForallF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.reForallStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.reForallChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.mapPairStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.mapPairStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.mapPairCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.lowOr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.lorStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.myLor
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.allListStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.existsListStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.allListChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.existsListChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.isBinDigit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.allBinDigitsChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.nthStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.nthCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.tabStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.tabCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.fuelTableStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.fuelTable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.mulBit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.decodeFuelOkCharBody
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.decodeFuelOkChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.decodeFuelOkCharLookup
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.listLenStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.listLenChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.natEqChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.listEqStpNonzero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.listEqStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.listEqStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.listEqChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.appendListTabFn
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.appendListCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.takeListTabFn
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.takeCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.dropListTabFn
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.dropCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.c9b5_boolNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.c9b5_encodeListBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.c9b5_sexprDepth
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.c9b5_sexprGodelEncode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.autStateCardFuelCharBody
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.autStateCardFuelChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.autStateCardFuelCharLookup
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.matchesBCatG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.matchesBCharBody
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.matchesBChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.matchesBCatGLookup
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.matchesBCharBodyLookup
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.codeBound
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.c9b6_decodeListBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.decideNonemptyBChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.capCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.consistentBChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.subsetBoundChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.subsetGuardChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.subsetBChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.interEqChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.amGM
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.iter_sq_le
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.lt_of_mul_lt_mul_left'
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.lt_iter_succ_sq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.sqrt_le
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.lt_succ_sqrt
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.sqrt_eq_of
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.sqrt_add_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_pair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_pair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_pair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.sqrt_le_add
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.pair_unpair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn_ite
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.le_pair_right
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_snd_le
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.isOne_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.isOne_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.isOne_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.natEqChar_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.listEqStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.c9b5_boolNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.c9b6_decodeListBool

@[expose] public section

/-!
# A choice-free recursion theory for Lecture VII (Scott 1981, PRG-19)

**Why this file exists — we roll our own and reject mathlib's recursion theory here.**
Lecture VII ("Computability in effectively given domains") needs the notions *recursively
decidable* and *recursively enumerable*. mathlib *has* these (`Computable`, `ComputablePred`,
`REPred`, `Primrec`, `Partrec`), but in mathlib `v4.30.0` essentially every *correctness lemma* of
that development is proved with tactics (`grind`, `lia`) or wrapper lemmas that **open
`Classical`** — e.g. `Computable.const`, `Primrec.const`, `Nat.unpair_pair`, `Nat.sqrt_le`, and
`Nat.Primrec.add`/`mul` all audit with `Classical.choice` in their axiom set. This project's
discipline is to keep *data* (and as much as possible) **choice-free** (`⊆ {propext, Quot.sound}`),
so we deliberately decline mathlib's classical recursion theory and instead build the slice we need
on the genuinely choice-free foundations: the raw inductives `Nat.Primrec` / `Nat.Partrec` (whose
*constructors* are choice-free) and `Nat.sqrt` / `Nat.pair` / `Nat.unpair` (whose *definitions* are
choice-free). The only tactic we lean on for arithmetic is `omega`, which is choice-free here
(unlike `grind`/`lia`).

The pattern: a relation on integer indices is *recursive* (decidable) when it has a
**primitive-recursive characteristic function** (`Nat.Primrec`, lifted to `Nat.Partrec` for the
recursive/`REPred` analogues). Tuples are encoded with `Nat.pair` (choice-free), and we reprove the
pairing round-trips (`unpair_pair'`, `pair_unpair'`) choice-free here.

Everything in this file is `⊆ {propext, Quot.sound}`.
-/

namespace Domain.Recursive

/-! ## Choice-free `Nat.sqrt` correctness

mathlib's `Nat.sqrt.iter_sq_le` / `Nat.sqrt.lt_iter_succ_sq` are the heart of `Nat.sqrt`'s
correctness, but they use `grind` / `lia` (classical). We reprove them with `omega`. -/


/-! ## Choice-free pairing round-trip

`Nat.pair`/`Nat.unpair` are themselves choice-free *definitions*; only mathlib's `unpair_pair`
*lemma* (via `sqrt_add_eq`) is classical. We reprove the round-trip on our choice-free `sqrt`. -/


/-! ## Choice-free primitive-recursive arithmetic

mathlib's `Nat.Primrec.id/add/mul` are proved with `by simp`, which silently applies the *classical*
`@[simp] Nat.unpair_pair`; so they audit with `Classical.choice`. We reprove the few we need using
the choice-free round-trips above. The *constructors* of `Nat.Primrec`
(`zero/succ/left/right/pair/comp/prec`) are choice-free and used directly. -/

/-- `id` is primitive recursive (choice-free). -/
theorem primrec_id : Nat.Primrec id :=
  (Nat.Primrec.left.pair Nat.Primrec.right).of_eq fun n => pair_unpair n

/-- The `prec` recursor for addition computes the sum. -/
theorem rec_add (a b : ℕ) : Nat.rec a (fun _ IH => IH + 1) b = a + b := by
  induction b with
  | zero => rfl
  | succ k ih => show Nat.rec a (fun _ IH => IH + 1) k + 1 = a + (k + 1); omega

/-- The `prec` recursor for multiplication computes the product. -/
private theorem rec_mul (a b : ℕ) : Nat.rec 0 (fun _ IH => a + IH) b = a * b := by
  induction b with
  | zero => rfl
  | succ k ih =>
    show a + Nat.rec 0 (fun _ IH => a + IH) k = a * (k + 1)
    rw [Nat.mul_succ]; omega

/-- Addition is primitive recursive (choice-free). -/
theorem primrec_add : Nat.Primrec (Nat.unpaired (· + ·)) :=
  (Nat.Primrec.prec primrec_id
      ((Nat.Primrec.succ.comp Nat.Primrec.right).comp Nat.Primrec.right)).of_eq fun p => by
    simp only [unpair_pair_snd, id_eq]
    exact rec_add _ _

/-- Multiplication is primitive recursive (choice-free). -/
theorem primrec_mul : Nat.Primrec (Nat.unpaired (· * ·)) :=
  (Nat.Primrec.prec Nat.Primrec.zero
      (primrec_add.comp (Nat.Primrec.pair Nat.Primrec.left
        (Nat.Primrec.right.comp Nat.Primrec.right)))).of_eq fun p => by
    simp only [unpair_pair_fst, unpair_pair_snd, Nat.unpaired]
    exact rec_mul _ _

/-- The `prec` recursor for predecessor computes `n - 1`. -/
private theorem rec_pred (n : ℕ) : Nat.rec 0 (fun y _ => y) n = n - 1 := by
  cases n with
  | zero => rfl
  | succ k => rfl

/-- Predecessor `n ↦ n - 1` is primitive recursive (choice-free; mathlib's `Nat.Primrec.pred` is
classical). -/
theorem primrec_pred : Nat.Primrec (fun n => n - 1) :=
  ((Nat.Primrec.prec Nat.Primrec.zero (Nat.Primrec.left.comp Nat.Primrec.right)).comp
    (primrec_id.pair primrec_id)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
    exact rec_pred n

/-- The `prec` recursor for truncated subtraction computes `a - b`. -/
private theorem rec_sub (a b : ℕ) : Nat.rec a (fun _ IH => IH - 1) b = a - b := by
  induction b with
  | zero => rfl
  | succ k ih => show Nat.rec a (fun _ IH => IH - 1) k - 1 = a - (k + 1); rw [ih]; omega

/-- Truncated subtraction is primitive recursive (choice-free; mathlib's `Nat.Primrec.sub` is
classical). -/
theorem primrec_sub : Nat.Primrec (Nat.unpaired (· - ·)) :=
  (Nat.Primrec.prec primrec_id
    ((primrec_pred.comp Nat.Primrec.right).comp Nat.Primrec.right)).of_eq fun p => by
    simp only [unpair_pair_snd, id_eq]
    exact rec_sub _ _

/-- `a * b = 1 ↔ a = 1 ∧ b = 1` over `ℕ` (choice-free; avoids the classical generic `mul_eq_one`). -/
theorem nat_mul_eq_one {a b : ℕ} : a * b = 1 ↔ a = 1 ∧ b = 1 := by
  refine ⟨fun h => ⟨Nat.dvd_one.mp ⟨b, h.symm⟩, Nat.dvd_one.mp ⟨a, ?_⟩⟩, fun h => by rw [h.1, h.2]⟩
  rw [Nat.mul_comm] at h; exact h.symm

/-! ## Pointwise primitive-recursive arithmetic combinators

`primrec_add`/`mul`/`sub` are `Nat.unpaired` forms; the `₂` variants below take two primitive
recursive functions `f, g` and build `fun n => f n ⋆ g n` directly (composing through `Nat.pair`).
These cut the `Nat.pair`/`unpair` plumbing in larger constructions (sum's intersection function and
the list-fold engine). All choice-free. -/

/-- `fun n => f n + g n` is primitive recursive. -/
theorem primrec_add₂ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => f n + g n) :=
  (primrec_add.comp (hf.pair hg)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]

/-- `fun n => f n * g n` is primitive recursive. -/
theorem primrec_mul₂ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => f n * g n) :=
  (primrec_mul.comp (hf.pair hg)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]

/-- `fun n => f n - g n` (truncated) is primitive recursive. -/
theorem primrec_sub₂ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => f n - g n) :=
  (primrec_sub.comp (hf.pair hg)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]


/-- `selectFn` of primitive-recursive `c, a, b` is primitive recursive. -/
theorem primrec_selectFn {c a b : ℕ → ℕ} (hc : Nat.Primrec c) (ha : Nat.Primrec a)
    (hb : Nat.Primrec b) : Nat.Primrec (fun n => selectFn (c n) (a n) (b n)) :=
  primrec_add₂ (primrec_mul₂ hc ha) (primrec_mul₂ (primrec_sub₂ (Nat.Primrec.const 1) hc) hb)


/-! ## "Recursively decidable" predicates (Scott's notion, Definition 7.1)

A predicate is recursively decidable when it has a primitive-recursive `{0,1}`-valued characteristic
function. Tuples are coded by `Nat.pair`. These are the building blocks Scott's Definition 7.1 needs
(relations on indices), and the closure lemmas (`of_iff`, `comp` = reindex, `and`) let us derive the
inclusion- and equality-deciders. All choice-free. -/


/-- Recursive decidability transfers across a pointwise logical equivalence. -/
theorem RecDecidable.of_iff {p q : ℕ → Prop} (h : ∀ n, q n ↔ p n) (hp : RecDecidable p) :
    RecDecidable q := by
  obtain ⟨f, hf, hfe⟩ := hp
  exact ⟨f, hf, fun n => (h n).trans (hfe n)⟩

/-- **Reindexing.** If `p` is recursively decidable and `g` is primitive recursive, then
`fun n => p (g n)` is recursively decidable. -/
theorem RecDecidable.comp {p : ℕ → Prop} (hp : RecDecidable p) {g : ℕ → ℕ}
    (hg : Nat.Primrec g) : RecDecidable (fun n => p (g n)) := by
  obtain ⟨f, hf, hfe⟩ := hp
  exact ⟨fun n => f (g n), hf.comp hg, fun n => hfe (g n)⟩

/-- **Conjunction.** Recursive decidability is closed under `∧` (multiply the `{0,1}` deciders). -/
theorem RecDecidable.and {p q : ℕ → Prop} (hp : RecDecidable p) (hq : RecDecidable q) :
    RecDecidable (fun n => p n ∧ q n) := by
  obtain ⟨f, hf, hfe⟩ := hp
  obtain ⟨g, hg, hge⟩ := hq
  refine ⟨fun n => f n * g n, ?_, fun n => ?_⟩
  · exact (primrec_mul.comp (hf.pair hg)).of_eq fun n => by
      simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  · rw [nat_mul_eq_one]; exact and_congr (hfe n) (hge n)

/-- **Equality of two primitive-recursive functions is recursively decidable.** The `{0,1}`-valued
characteristic function is `1 - ((a t - b t) + (b t - a t))` (truncated subtraction), which is `1`
exactly when `a t = b t`; primitive recursive via `primrec_sub`/`primrec_add`, and the biconditional
is `omega` (which understands truncated subtraction). -/
theorem RecDecidable.natEq {a b : ℕ → ℕ} (ha : Nat.Primrec a) (hb : Nat.Primrec b) :
    RecDecidable (fun t => a t = b t) := by
  refine ⟨fun t => Nat.unpaired (· - ·) (Nat.pair 1 (Nat.unpaired (· + ·)
      (Nat.pair (Nat.unpaired (· - ·) (Nat.pair (a t) (b t)))
        (Nat.unpaired (· - ·) (Nat.pair (b t) (a t)))))), ?_, fun t => ?_⟩
  · exact primrec_sub.comp ((Nat.Primrec.const 1).pair (primrec_add.comp
      ((primrec_sub.comp (ha.pair hb)).pair (primrec_sub.comp (hb.pair ha)))))
  · simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
    constructor <;> intro h <;> omega

/-- **Negation.** Recursive decidability is closed under `¬` (negate the `{0,1}` decider). -/
theorem RecDecidable.not {p : ℕ → Prop} (hp : RecDecidable p) : RecDecidable (fun n => ¬ p n) := by
  obtain ⟨f, hf, hfe⟩ := hp
  refine ⟨fun n => Nat.unpaired (· - ·) (Nat.pair 1 (Nat.unpaired (· - ·) (Nat.pair 1
      (Nat.unpaired (· + ·) (Nat.pair (Nat.unpaired (· - ·) (Nat.pair (f n) 1))
        (Nat.unpaired (· - ·) (Nat.pair 1 (f n)))))))), ?_, fun n => ?_⟩
  · exact primrec_sub.comp ((Nat.Primrec.const 1).pair (primrec_sub.comp
      ((Nat.Primrec.const 1).pair (primrec_add.comp
        ((primrec_sub.comp (hf.pair (Nat.Primrec.const 1))).pair
          (primrec_sub.comp ((Nat.Primrec.const 1).pair hf)))))))
  · show ¬ p n ↔ _
    rw [hfe n]
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
    constructor <;> intro h <;> omega

/-- Every recursively decidable predicate is **decidable** (the decider is `f n = 1`, decidable
equality on `ℕ`); useful for choice-free De Morgan. -/
theorem RecDecidable.em {p : ℕ → Prop} (hp : RecDecidable p) (n : ℕ) : p n ∨ ¬ p n := by
  obtain ⟨f, _, hfe⟩ := hp
  by_cases h : f n = 1
  · exact Or.inl ((hfe n).mpr h)
  · exact Or.inr (fun hp => h ((hfe n).mp hp))

/-- **Disjunction.** Recursive decidability is closed under `∨`, via choice-free De Morgan
`p ∨ q ↔ ¬(¬p ∧ ¬q)` (the non-constructive direction uses `RecDecidable.em`). -/
theorem RecDecidable.or {p q : ℕ → Prop} (hp : RecDecidable p) (hq : RecDecidable q) :
    RecDecidable (fun n => p n ∨ q n) := by
  refine RecDecidable.of_iff (fun n => ?_) (hp.not.and hq.not).not
  constructor
  · rintro (h | h) ⟨hnp, hnq⟩
    · exact hnp h
    · exact hnq h
  · intro h
    rcases hp.em n with hp' | hp'
    · exact Or.inl hp'
    · rcases hq.em n with hq' | hq'
      · exact Or.inr hq'
      · exact absurd ⟨hp', hq'⟩ h

/-! ## "Recursively enumerable" predicates (Scott's notion, Definition 7.2)

Scott's Definition 7.2 asks for the neighbourhood relation `Xₙ f Yₘ` to be *recursively
enumerable*. We model "recursively enumerable" choice-free as a **projection of a recursively
decidable relation**: `p` is r.e. iff there is a recursively decidable `q` with
`p n ↔ ∃ i, q ⟨i, n⟩` (the search variable `i` is paired with `n` via `Nat.pair`). This is the
standard equivalent of Scott's prose description — "there is a primitive recursive `r` with
`y = {Y_{r(i)} ∣ i ∈ ℕ}`": the projection form additionally represents the empty set (take `q`
identically false), exactly as r.e. sets require. Every recursively decidable predicate is r.e.
(`RecDecidable.re`, dropping the search variable), and r.e.-ness transfers across pointwise
equivalence (`REPred.of_iff`). All choice-free. -/


/-- **Every recursively decidable predicate is recursively enumerable.** Use the decider as the
relation `q ⟨i, n⟩ := p n` (a reindex of `p` along `unpair.2`, dropping the search variable `i`); the
witness `i = 0` makes the projection trivial. -/
theorem RecDecidable.re {p : ℕ → Prop} (hp : RecDecidable p) : REPred p := by
  refine ⟨fun t => p t.unpair.2, hp.comp Nat.Primrec.right, fun n => ?_⟩
  simp only [unpair_pair_snd]
  exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩

/-- A recursively decidable binary relation is recursively enumerable. -/
theorem RecDecidable₂.re {r : ℕ → ℕ → Prop} (hr : RecDecidable₂ r) : REPred₂ r :=
  RecDecidable.re hr

/-- Recursive enumerability transfers across a pointwise logical equivalence. -/
theorem REPred.of_iff {p q : ℕ → Prop} (h : ∀ n, q n ↔ p n) (hp : REPred p) : REPred q := by
  obtain ⟨r, hr, hre⟩ := hp
  exact ⟨r, hr, fun n => (h n).trans (hre n)⟩

/-! ### Closure properties of r.e. predicates (for Proposition 7.3 and Theorem 7.4)

The projection-of-decidable form makes r.e.-ness closed under primitive-recursive **reindexing**
(`REPred.comp`), **conjunction** (`REPred.and`, pairing the two search variables), and
**existential projection** over `ℕ` (`REPred.proj`, absorbing the projected variable into the search
variable). These are exactly the moves Scott's `g ∘ f` needs: `X (g∘f) Z ↔ ∃ Y, X f Y ∧ Y g Z`. -/

/-- **Reindexing.** If `p` is r.e. and `g` is primitive recursive, then `fun n => p (g n)` is r.e.
(absorb `g` into the decidable relation along `unpair.2`). -/
theorem REPred.comp {p : ℕ → Prop} (hp : REPred p) {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    REPred (fun n => p (g n)) := by
  obtain ⟨q, hq, hqe⟩ := hp
  refine ⟨fun t => q (Nat.pair t.unpair.1 (g t.unpair.2)),
    hq.comp (Nat.Primrec.left.pair (hg.comp Nat.Primrec.right)), fun n => ?_⟩
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact hqe (g n)

/-- **Conjunction.** Recursive enumerability is closed under `∧`: combine the two decidable relations
and run the two searches in parallel (pairing the search variables `i, j` into a single `w`). -/
theorem REPred.and {p q : ℕ → Prop} (hp : REPred p) (hq : REPred q) :
    REPred (fun n => p n ∧ q n) := by
  obtain ⟨a, ha, hae⟩ := hp
  obtain ⟨b, hb, hbe⟩ := hq
  refine ⟨fun u => a (Nat.pair u.unpair.1.unpair.1 u.unpair.2)
      ∧ b (Nat.pair u.unpair.1.unpair.2 u.unpair.2),
    (ha.comp ((Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right)).and
      (hb.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right)), fun n => ?_⟩
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hae n, hbe n]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨Nat.pair i j, by simp only [unpair_pair_fst, unpair_pair_snd]; exact ⟨hi, hj⟩⟩
  · rintro ⟨w, hw1, hw2⟩
    exact ⟨⟨w.unpair.1, hw1⟩, ⟨w.unpair.2, hw2⟩⟩

/-- **Existential projection.** If `p` is r.e. then so is `fun n => ∃ i, p ⟨i, n⟩`: fold the new
existential variable `i` into the search variable (pairing it with the decidable relation's own
search variable `j`). -/
theorem REPred.proj {p : ℕ → Prop} (hp : REPred p) :
    REPred (fun n => ∃ i, p (Nat.pair i n)) := by
  obtain ⟨q, hq, hqe⟩ := hp
  refine ⟨fun u => q (Nat.pair u.unpair.1.unpair.2 (Nat.pair u.unpair.1.unpair.1 u.unpair.2)),
    hq.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
      ((Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right)), fun n => ?_⟩
  simp only [unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨i, hi⟩
    rw [hqe (Nat.pair i n)] at hi
    obtain ⟨j, hj⟩ := hi
    exact ⟨Nat.pair i j, by simpa only [unpair_pair_fst, unpair_pair_snd] using hj⟩
  · rintro ⟨w, hw⟩
    refine ⟨w.unpair.1, ?_⟩
    rw [hqe (Nat.pair w.unpair.1 n)]
    exact ⟨w.unpair.2, hw⟩

/-- **Disjunction of r.e. predicates is r.e.** A witness `w` carries a tag `w.1 ∈ {0,1}` selecting
which disjunct's search index `w.2` to use; the underlying relation is recursively decidable by
`RecDecidable.or`/`.and`/`.natEq`. (Used for the sum-mapping `f + g` of Theorem 7.4.) -/
theorem REPred.or {p q : ℕ → Prop} (hp : REPred p) (hq : REPred q) :
    REPred (fun n => p n ∨ q n) := by
  obtain ⟨a, ha, hae⟩ := hp
  obtain ⟨b, hb, hbe⟩ := hq
  refine ⟨fun u => (a (Nat.pair u.unpair.1.unpair.2 u.unpair.2) ∧ u.unpair.1.unpair.1 = 0)
      ∨ (b (Nat.pair u.unpair.1.unpair.2 u.unpair.2) ∧ u.unpair.1.unpair.1 = 1), ?_, fun n => ?_⟩
  · refine RecDecidable.or (RecDecidable.and ?_ ?_) (RecDecidable.and ?_ ?_)
    · exact ha.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right)
    · exact RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
    · exact hb.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right)
    · exact RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  · show p n ∨ q n ↔ _
    rw [hae n, hbe n]
    constructor
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · refine ⟨Nat.pair 0 i, Or.inl ⟨?_, ?_⟩⟩
        · simpa only [unpair_pair_fst, unpair_pair_snd] using hi
        · simp only [unpair_pair_fst]
      · refine ⟨Nat.pair 1 i, Or.inr ⟨?_, ?_⟩⟩
        · simpa only [unpair_pair_fst, unpair_pair_snd] using hi
        · simp only [unpair_pair_fst]
    · rintro ⟨w, hw⟩
      simp only [unpair_pair_fst, unpair_pair_snd] at hw
      rcases hw with ⟨hi, _⟩ | ⟨hi, _⟩
      · exact Or.inl ⟨w.unpair.2, hi⟩
      · exact Or.inr ⟨w.unpair.2, hi⟩

/-! ## A choice-free primitive-recursive fold engine over `Nat`-coded lists

Scott's function-space deciders (Theorem 7.5) range over *finite lists* of neighborhood indices.
To stay choice-free we encode such a list as a single natural via `encodeList` and process it with a
genuinely primitive-recursive `foldCode`. The key results are:

* `encodeList`            — `List ℕ → ℕ`, with `l.length ≤ encodeList l` (`encodeList_length_le`);
* `foldCode stp p z c`    — folds the list coded by `c`, threading an accumulator and a fixed
                            parameter `p`, with `stp` the (coded) step function;
* `foldCode_eq`           — `foldCode` on `encodeList l` equals the corresponding `List.foldl`;
* `primrec_foldCode`      — `foldCode` is primitive recursive in all of its (primrec) inputs.

`foldStep` walks one entry: the state is `pair remainingCode accumulator`; an empty remaining code
(`= 0`) is a fixed point, otherwise it pops the head and applies `stp`. -/


/-- `a ≤ pair a b` (choice-free). -/
theorem le_pair_left (a b : ℕ) : a ≤ Nat.pair a b := by
  unfold Nat.pair
  split <;> omega


/-- The length of a list is bounded by its code; this is the fuel bound that lets a `c`-fold iterate
enough times to consume the whole list coded by `c`. -/
theorem encodeList_length_le : ∀ l : List ℕ, l.length ≤ encodeList l
  | [] => Nat.le_refl 0
  | a :: l => by
    simp only [encodeList, List.length_cons]
    have hrec := encodeList_length_le l
    have hle : encodeList l ≤ Nat.pair a (encodeList l) := le_pair_right a (encodeList l)
    omega


/-- Empty remaining code: the fold state is unchanged. -/
theorem foldStep_zero (stp : ℕ → ℕ) (params acc : ℕ) :
    foldStep stp params (Nat.pair 0 acc) = Nat.pair 0 acc := by
  unfold foldStep
  simp only [unpair_pair_fst, unpair_pair_snd, Nat.sub_zero, selectFn_one]

/-- Nonempty remaining code `pair a t + 1`: pop `a`, recurse on `t`, update the accumulator. -/
theorem foldStep_pos (stp : ℕ → ℕ) (params a t acc : ℕ) :
    foldStep stp params (Nat.pair (Nat.pair a t + 1) acc)
      = Nat.pair t (stp (Nat.pair a (Nat.pair acc params))) := by
  unfold foldStep
  simp only [unpair_pair_fst, unpair_pair_snd]
  have h1 : 1 - (Nat.pair a t + 1) = 0 := by omega
  have h2 : Nat.pair a t + 1 - 1 = Nat.pair a t := by omega
  rw [h1, h2, selectFn_zero, unpair_pair_fst, unpair_pair_snd]


/-- `Nat.rec` with a counter-independent step is just function iteration (choice-free). Needed to
bridge the `Nat.Primrec.prec` form (a `Nat.rec`) with `foldCode`'s `Function.iterate` form. -/
theorem rec_const_iterate (f : ℕ → ℕ) (s : ℕ) :
    ∀ k : ℕ, Nat.rec (motive := fun _ => ℕ) s (fun _ ih => f ih) k = f^[k] s
  | 0 => rfl
  | (k + 1) => by
      rw [Function.iterate_succ_apply']
      exact congrArg f (rec_const_iterate f s k)

/-- Core correctness of the iteration: starting from `pair (encodeList l) acc`, after at least
`l.length` steps the accumulator equals the `List.foldl` of the step over `l`. -/
theorem foldStep_iterate (stp : ℕ → ℕ) (params : ℕ) :
    ∀ (k : ℕ) (l : List ℕ) (acc : ℕ), l.length ≤ k →
      ((foldStep stp params)^[k] (Nat.pair (encodeList l) acc)).unpair.2
        = List.foldl (fun acc x => stp (Nat.pair x (Nat.pair acc params))) acc l := by
  intro k
  induction k with
  | zero =>
    intro l acc hlen
    cases l with
    | nil => simp only [Function.iterate_zero_apply, encodeList, unpair_pair_snd, List.foldl_nil]
    | cons a l' => simp only [List.length_cons] at hlen; omega
  | succ k ih =>
    intro l acc hlen
    rw [Function.iterate_succ_apply]
    cases l with
    | nil =>
      rw [show encodeList ([] : List ℕ) = 0 from rfl, foldStep_zero]
      exact ih [] acc (Nat.zero_le k)
    | cons a l' =>
      have hlen' : l'.length ≤ k := by simp only [List.length_cons] at hlen; omega
      rw [show encodeList (a :: l') = Nat.pair a (encodeList l') + 1 from rfl, foldStep_pos,
        ih l' (stp (Nat.pair a (Nat.pair acc params))) hlen', List.foldl_cons]

/-- **Correctness of `foldCode`.** Folding the code of `l` equals the corresponding `List.foldl`. -/
theorem foldCode_eq (stp : ℕ → ℕ) (params z : ℕ) (l : List ℕ) :
    foldCode stp params z (encodeList l)
      = List.foldl (fun acc x => stp (Nat.pair x (Nat.pair acc params))) z l := by
  unfold foldCode
  exact foldStep_iterate stp params (encodeList l) l z (encodeList_length_le l)


theorem unpair_left_le (n : ℕ) : n.unpair.1 ≤ n := by
  have h := le_pair_left n.unpair.1 n.unpair.2
  rwa [pair_unpair] at h

/-- Weak version of mathlib's `Nat.pair_lt_pair_left`. -/
theorem pair_le_pair_left (b : ℕ) {a a' : ℕ} (h : a ≤ a') : Nat.pair a b ≤ Nat.pair a' b := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_refl _
  · exact le_of_lt (Nat.pair_lt_pair_left b hlt)

/-- Weak version of mathlib's `Nat.pair_lt_pair_right`. -/
theorem pair_le_pair_right' (a : ℕ) {b b' : ℕ} (h : b ≤ b') : Nat.pair a b ≤ Nat.pair a b' := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_refl _
  · exact le_of_lt (Nat.pair_lt_pair_right a hlt)

/-- `Nat.pair` is weakly monotone in both arguments jointly. -/
theorem pair_le_pair {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    Nat.pair a b ≤ Nat.pair a' b' :=
  le_trans (pair_le_pair_left b ha) (pair_le_pair_right' a' hb)


theorem decodeList_zero : decodeList 0 = [] := by rw [decodeList]

theorem decodeList_succ (c : ℕ) :
    decodeList (c + 1) = c.unpair.1 :: decodeList c.unpair.2 := by
  rw [decodeList]

/-- `encodeList ∘ decodeList = id`: every natural is the code of its decoded list. -/
theorem encodeList_decodeList (c : ℕ) : encodeList (decodeList c) = c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    cases c with
    | zero => simp only [decodeList_zero, encodeList]
    | succ d =>
      rw [decodeList_succ, encodeList, ih d.unpair.2 (Nat.lt_succ_of_le (unpair_snd_le d)),
        pair_unpair]

/-- **Correctness of `foldCode` on an arbitrary code.** `foldCode` over any natural `c` equals the
`List.foldl` over the list `c` decodes to. -/
theorem foldCode_eq' (stp : ℕ → ℕ) (params z c : ℕ) :
    foldCode stp params z c
      = List.foldl (fun acc x => stp (Nat.pair x (Nat.pair acc params))) z (decodeList c) := by
  conv_lhs => rw [← encodeList_decodeList c]
  rw [foldCode_eq]

/-- `foldStep` (with the parameter packed into the state as `pair params state`) is primitive
recursive whenever the step `stp` is. This is the workhorse for `primrec_foldCode`. -/
theorem primrec_foldStepPacked {stp : ℕ → ℕ} (hstp : Nat.Primrec stp) :
    Nat.Primrec (fun w => foldStep stp w.unpair.1 w.unpair.2) := by
  have hparams : Nat.Primrec (fun w => w.unpair.1) := Nat.Primrec.left
  have hstate : Nat.Primrec (fun w => w.unpair.2) := Nat.Primrec.right
  have hrc : Nat.Primrec (fun w => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hacc : Nat.Primrec (fun w => w.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hcond : Nat.Primrec (fun w => 1 - w.unpair.2.unpair.1) :=
    primrec_sub₂ (Nat.Primrec.const 1) hrc
  have hrcm1 : Nat.Primrec (fun w => w.unpair.2.unpair.1 - 1) :=
    primrec_sub₂ hrc (Nat.Primrec.const 1)
  have hhead : Nat.Primrec (fun w => (w.unpair.2.unpair.1 - 1).unpair.1) :=
    Nat.Primrec.left.comp hrcm1
  have htail : Nat.Primrec (fun w => (w.unpair.2.unpair.1 - 1).unpair.2) :=
    Nat.Primrec.right.comp hrcm1
  have hinner : Nat.Primrec (fun w => Nat.pair w.unpair.2.unpair.2 w.unpair.1) := hacc.pair hparams
  have harg : Nat.Primrec
      (fun w => Nat.pair (w.unpair.2.unpair.1 - 1).unpair.1
        (Nat.pair w.unpair.2.unpair.2 w.unpair.1)) := hhead.pair hinner
  have hstpv : Nat.Primrec
      (fun w => stp (Nat.pair (w.unpair.2.unpair.1 - 1).unpair.1
        (Nat.pair w.unpair.2.unpair.2 w.unpair.1))) := hstp.comp harg
  have helse : Nat.Primrec
      (fun w => Nat.pair (w.unpair.2.unpair.1 - 1).unpair.2
        (stp (Nat.pair (w.unpair.2.unpair.1 - 1).unpair.1
          (Nat.pair w.unpair.2.unpair.2 w.unpair.1)))) := htail.pair hstpv
  exact (primrec_selectFn hcond hstate helse).of_eq fun _ => rfl

/-- **`foldCode` is primitive recursive** in all of its (primitive-recursive) inputs. -/
theorem primrec_foldCode {stp : ℕ → ℕ} (hstp : Nat.Primrec stp)
    {params z c : ℕ → ℕ} (hp : Nat.Primrec params) (hz : Nat.Primrec z) (hc : Nat.Primrec c) :
    Nat.Primrec (fun n => foldCode stp (params n) (z n) (c n)) := by
  have hfoldw : Nat.Primrec (fun w => foldStep stp w.unpair.1 w.unpair.2) :=
    primrec_foldStepPacked hstp
  have hg : Nat.Primrec (fun x => foldStep stp x.unpair.1.unpair.1 x.unpair.2.unpair.2) :=
    (hfoldw.comp ((Nat.Primrec.left.comp Nat.Primrec.left).pair
      (Nat.Primrec.right.comp Nat.Primrec.right))).of_eq fun _ => by
        simp only [unpair_pair_fst, unpair_pair_snd]
  have hprec := Nat.Primrec.prec Nat.Primrec.right hg
  refine (Nat.Primrec.right.comp
    (hprec.comp ((hp.pair (hc.pair hz)).pair hc))).of_eq fun n => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  rw [rec_const_iterate]
  rfl

/-! ## Primitive-recursive exponentiation (for the `2^q` subset bound)

The funSpace consistency decider quantifies over all `2^q` subsets of a `q`-element step-list, so it
needs `2^q` as a primitive-recursive bound. Choice-free (mathlib's `Nat.Primrec` lemmas for `^` route
through classical `simp`). -/

/-! ## Halving (`/2`, `%2`) for per-subset bit extraction

The funSpace consistency fold walks a step-list while consuming a subset bitmask `b` one bit at a
time: at each entry it reads `b % 2` (is this entry in the subset?) and recurses on `b / 2`. Only
division/modulus by the literal `2` is needed — which `omega` discharges directly — so this stays
choice-free without a general `div`/`mod`. Computed jointly by `halfParity n = pair (n/2) (n%2)`. -/


/-! ## Bounded quantifiers for recursively decidable predicates

Scott's function-space consistency decider (Theorem 7.5) is a *bounded universal* statement: a list of
step-pairs is consistent iff for **every** subset (coded by a bitmask `b < 2^q`) a component condition
holds. Bounded quantification of a recursively decidable predicate is again recursively decidable —
choice-free, via an explicit `Nat.rec` fold of the `{0,1}` indicator. -/


theorem isOne_le_one (v : ℕ) : isOne v ≤ 1 := by unfold isOne; omega


theorem isOne_of_ne_one {v : ℕ} (h : v ≠ 1) : isOne v = 0 := by
  unfold isOne
  omega

theorem primrec_isOne : Nat.Primrec isOne :=
  primrec_sub₂ (Nat.Primrec.const 1)
    (primrec_add₂ (primrec_sub₂ primrec_id (Nat.Primrec.const 1))
      (primrec_sub₂ (Nat.Primrec.const 1) primrec_id))


theorem isZero_eq_one_iff (n : ℕ) : isZero n = 1 ↔ n = 0 := by
  unfold isZero; omega

theorem isZero_le_one (n : ℕ) : isZero n ≤ 1 := by unfold isZero; omega

theorem primrec_isZero : Nat.Primrec isZero := by
  have hmin : Nat.Primrec (fun n => min n 1) :=
    (primrec_sub₂ primrec_id (primrec_sub₂ primrec_id (Nat.Primrec.const 1))).of_eq fun n => by
      rcases n with _ | n
      · rfl
      · show n + 1 - (n + 1 - 1) = min (n + 1) 1
        rw [Nat.min_eq_right (Nat.le_add_left 1 n)]
        omega
  exact primrec_sub₂ (Nat.Primrec.const 1) hmin

/-- `{0,1}` test for `f n ≤ g n` (truncated subtraction). -/
theorem primrec_le {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => isZero (f n - g n)) :=
  primrec_isZero.comp (primrec_sub₂ hf hg)


theorem bForallFn_le_one (g : ℕ → ℕ) (n N : ℕ) : bForallFn g n N ≤ 1 := by
  induction N with
  | zero => exact Nat.le_refl 1
  | succ N ih =>
    show selectFn (bForallFn g n N) (isOne (g (Nat.pair N n))) 0 ≤ 1
    rcases (show bForallFn g n N = 0 ∨ bForallFn g n N = 1 by omega) with h | h
    · rw [h, selectFn_zero]; exact Nat.zero_le 1
    · rw [h, selectFn_one]; exact isOne_le_one _

theorem bForallFn_eq_one_iff (g : ℕ → ℕ) (n N : ℕ) :
    bForallFn g n N = 1 ↔ ∀ i, i < N → g (Nat.pair i n) = 1 := by
  induction N with
  | zero =>
    constructor
    · intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
    · intro _; rfl
  | succ N ih =>
    have hstep : bForallFn g n (N + 1)
        = selectFn (bForallFn g n N) (isOne (g (Nat.pair N n))) 0 := rfl
    have hle := bForallFn_le_one g n N
    rw [hstep]
    rcases (show bForallFn g n N = 0 ∨ bForallFn g n N = 1 by omega) with h0 | h1
    · rw [h0, selectFn_zero]
      constructor
      · intro hcontra; exact absurd hcontra (by decide)
      · intro hall
        have hb : bForallFn g n N = 1 := ih.mpr (fun i hi => hall i (Nat.lt_succ_of_lt hi))
        rw [h0] at hb; exact hb
    · rw [h1, selectFn_one, isOne_eq_one_iff]
      constructor
      · intro hgN i hi
        rcases (show i < N ∨ i = N by omega) with hlt | heq
        · exact (ih.mp h1) i hlt
        · subst heq; exact hgN
      · intro hall; exact hall N (Nat.lt_succ_self N)


theorem bExistsFn_le_one (g : ℕ → ℕ) (n N : ℕ) : bExistsFn g n N ≤ 1 := by
  induction N with
  | zero => simp [bExistsFn]
  | succ N ih =>
    show selectFn (bExistsFn g n N) 1 (isOne (g (Nat.pair N n))) ≤ 1
    rcases (show bExistsFn g n N = 0 ∨ bExistsFn g n N = 1 by omega) with h | h
    · rw [h, selectFn_zero]
      exact isOne_le_one _
    · rw [h, selectFn_one]

/-- `bExistsFn` only depends on `g` through its values on the search range `{pair i n | i < N}`. -/
theorem bExistsFn_congr {g1 g2 : ℕ → ℕ} {n N : ℕ}
    (h : ∀ i < N, g1 (Nat.pair i n) = g2 (Nat.pair i n)) : bExistsFn g1 n N = bExistsFn g2 n N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    show selectFn (bExistsFn g1 n N) 1 (isOne (g1 (Nat.pair N n)))
      = selectFn (bExistsFn g2 n N) 1 (isOne (g2 (Nat.pair N n)))
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h N (Nat.lt_succ_self N)]

theorem bExistsFn_eq_one_iff (g : ℕ → ℕ) (n N : ℕ) :
    bExistsFn g n N = 1 ↔ ∃ i, i < N ∧ g (Nat.pair i n) = 1 := by
  induction N with
  | zero =>
    simp [bExistsFn]
  | succ N ih =>
    have hstep : bExistsFn g n (N + 1)
        = selectFn (bExistsFn g n N) 1 (isOne (g (Nat.pair N n))) := rfl
    rw [hstep]
    have hle := bExistsFn_le_one g n N
    rcases (show bExistsFn g n N = 0 ∨ bExistsFn g n N = 1 by omega) with h0 | h1
    · rw [h0, selectFn_zero, isOne_eq_one_iff]
      constructor
      · intro hgN; exact ⟨N, Nat.lt_succ_self N, hgN⟩
      · intro ⟨i, hi, hg⟩
        rcases (show i < N ∨ i = N by omega) with hlt | heq
        · have hne : bExistsFn g n N = 1 := ih.mpr ⟨i, hlt, hg⟩
          omega
        · subst heq; exact hg
    · rw [h1, selectFn_one]
      constructor
      · intro _
        obtain ⟨i, hi, hg⟩ := ih.mp h1
        exact ⟨i, Nat.lt_succ_of_lt hi, hg⟩
      · intro _; rfl

theorem primrec_bExistsFn {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (fun t => bExistsFn g t.unpair.1 t.unpair.2) := by
  have hGfn : Nat.Primrec (fun w =>
      selectFn w.unpair.2.unpair.2 1 (isOne (g (Nat.pair w.unpair.2.unpair.1 w.unpair.1)))) :=
    primrec_selectFn (Nat.Primrec.right.comp Nat.Primrec.right)
      (Nat.Primrec.const 1)
      (primrec_isOne.comp (hg.comp
        ((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left)))
  have hprec := Nat.Primrec.prec (Nat.Primrec.const 0) hGfn
  refine (hprec.comp (Nat.Primrec.left.pair Nat.Primrec.right)).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  rfl

/-- Parametrized variant of `primrec_bExistsFn`: `g` may also depend on an external `param`
(e.g. `fuel`) held fixed throughout the search, packed as `t.unpair.1.unpair.1`. Needed once `g`
itself is only jointly (not per-fixed-`param`) primitive recursive. -/
theorem primrec_bExistsFn_param {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (fun t => bExistsFn (fun p => g (Nat.pair t.unpair.1.unpair.1 p))
      t.unpair.1.unpair.2 t.unpair.2) := by
  have hGfn : Nat.Primrec (fun w =>
      selectFn w.unpair.2.unpair.2 1
        (isOne (g (Nat.pair w.unpair.1.unpair.1
          (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2))))) :=
    primrec_selectFn (Nat.Primrec.right.comp Nat.Primrec.right)
      (Nat.Primrec.const 1)
      (primrec_isOne.comp (hg.comp
        (Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.left)
          (Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.right)
            (Nat.Primrec.right.comp Nat.Primrec.left)))))
  have hprec := Nat.Primrec.prec (Nat.Primrec.const 0) hGfn
  refine (hprec.comp (Nat.Primrec.left.pair Nat.Primrec.right)).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  rfl

/-- `decodeList ∘ encodeList = id` (the round-trip the other way from `encodeList_decodeList`). -/
theorem decodeList_encodeList : ∀ l : List ℕ, decodeList (encodeList l) = l
  | [] => by rw [encodeList, decodeList_zero]
  | a :: l => by
    rw [encodeList, decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_encodeList l]

/-! ## Bounded universal quantification of an r.e. predicate over a coded list

The "computable elements = computable maps" half of Theorem 7.5 needs r.e.-ness closed under
`∀ e ∈ decodeList c, p e` for an r.e. `p`. Classically this is the standard "bounded `∀` of r.e. is
r.e."; choice-free we realise the search for the finite tuple of witnesses as a *single* code `w`
whose decoded list supplies one witness per list entry, threaded through a `foldCode`. -/


theorem reForallStp_eq (qc : ℕ → ℕ) (acc x : ℕ) :
    reForallStp qc (Nat.pair x (Nat.pair acc 0)) = reForallF qc acc x := by
  unfold reForallStp reForallF
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem reForallChar_eq (qc : ℕ → ℕ) (w c : ℕ) :
    reForallChar qc w c
      = (List.foldl (reForallF qc) (Nat.pair w 1) (decodeList c)).unpair.2 := by
  have hfun : (fun (acc x : ℕ) => reForallStp qc (Nat.pair x (Nat.pair acc 0))) = reForallF qc := by
    funext acc x; exact reForallStp_eq qc acc x
  unfold reForallChar
  rw [foldCode_eq', hfun]

/-- **Core induction.** Threading witness code `w` through `l`, the final flag is `1` iff the start
flag was `1` and, position by position, the `k`-th witness of `decodeList w` satisfies `qc`. -/
theorem reForallF_foldl_eq_one_iff (qc : ℕ → ℕ) :
    ∀ (l : List ℕ) (w flag : ℕ), flag ≤ 1 →
      ((List.foldl (reForallF qc) (Nat.pair w flag) l).unpair.2 = 1 ↔
        flag = 1 ∧ ∀ k, k < l.length →
          qc (Nat.pair ((decodeList w).getD k 0) (l.getD k 0)) = 1) := by
  intro l
  induction l with
  | nil =>
    intro w flag _
    simp only [List.foldl_nil, unpair_pair_snd, List.length_nil, Nat.not_lt_zero,
      false_implies, implies_true, and_true]
  | cons x l ih =>
    intro w flag hflag
    have hi : (decodeList w).getD 0 0 = (w - 1).unpair.1 := by
      rcases w with _ | c
      · have hz : ((0 : ℕ) - 1).unpair.1 = 0 := by
          rw [Nat.zero_sub]; exact congrArg Prod.fst Nat.unpair_zero
        rw [decodeList_zero, List.getD_nil, hz]
      · rw [decodeList_succ, List.getD_cons_zero, Nat.add_sub_cancel]
    have htail : ∀ k, (decodeList w).getD (k + 1) 0 = (decodeList (w - 1).unpair.2).getD k 0 := by
      intro k
      rcases w with _ | c
      · have hz : ((0 : ℕ) - 1).unpair.2 = 0 := by
          rw [Nat.zero_sub]; exact congrArg Prod.snd Nat.unpair_zero
        rw [decodeList_zero, hz, decodeList_zero, List.getD_nil, List.getD_nil]
      · rw [decodeList_succ, List.getD_cons_succ, Nat.add_sub_cancel]
    have hstep : List.foldl (reForallF qc) (Nat.pair w flag) (x :: l)
        = List.foldl (reForallF qc) (Nat.pair (w - 1).unpair.2
            (selectFn flag (isOne (qc (Nat.pair (w - 1).unpair.1 x))) 0)) l := by
      rw [List.foldl_cons]
      congr 1
      show reForallF qc (Nat.pair w flag) x = _
      unfold reForallF
      rw [unpair_pair_fst, unpair_pair_snd]
    rw [hstep]
    set flag' := selectFn flag (isOne (qc (Nat.pair (w - 1).unpair.1 x))) 0 with hflag'def
    have hflag'le : flag' ≤ 1 := by
      rw [hflag'def]
      rcases (show flag = 0 ∨ flag = 1 by omega) with h | h
      · rw [h, selectFn_zero]; exact Nat.zero_le 1
      · rw [h, selectFn_one]; exact isOne_le_one _
    rw [ih (w - 1).unpair.2 flag' hflag'le]
    constructor
    · rintro ⟨hf', hrest⟩
      have hsplit : flag = 1 ∧ qc (Nat.pair (w - 1).unpair.1 x) = 1 := by
        rw [hflag'def] at hf'
        rcases (show flag = 0 ∨ flag = 1 by omega) with h | h
        · rw [h, selectFn_zero] at hf'; exact absurd hf' (by decide)
        · rw [h, selectFn_one, isOne_eq_one_iff] at hf'; exact ⟨h, hf'⟩
      refine ⟨hsplit.1, fun k hk => ?_⟩
      rcases k with _ | k'
      · rw [List.getD_cons_zero, hi]; exact hsplit.2
      · rw [List.getD_cons_succ, htail]
        exact hrest k' (by simp only [List.length_cons] at hk; omega)
    · rintro ⟨hflag1, hall⟩
      have hhead : qc (Nat.pair (w - 1).unpair.1 x) = 1 := by
        have := hall 0 (by simp only [List.length_cons]; omega)
        rwa [List.getD_cons_zero, hi] at this
      refine ⟨?_, fun k hk => ?_⟩
      · rw [hflag'def, hflag1, selectFn_one, isOne_eq_one_iff]; exact hhead
      · have := hall (k + 1) (by simp only [List.length_cons]; omega)
        rwa [List.getD_cons_succ, htail] at this

theorem reForallChar_eq_one_iff (qc : ℕ → ℕ) (w c : ℕ) :
    reForallChar qc w c = 1 ↔
      ∀ k, k < (decodeList c).length →
        qc (Nat.pair ((decodeList w).getD k 0) ((decodeList c).getD k 0)) = 1 := by
  rw [reForallChar_eq, reForallF_foldl_eq_one_iff qc (decodeList c) w 1 (Nat.le_refl 1)]
  simp only [true_and]

theorem primrec_reForallStp {qc : ℕ → ℕ} (hqc : Nat.Primrec qc) :
    Nat.Primrec (reForallStp qc) := by
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hrw : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp hacc
  have hflag : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp hacc
  have hpm : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1 - 1) :=
    primrec_sub₂ hrw (Nat.Primrec.const 1)
  have hi : Nat.Primrec (fun w : ℕ => (w.unpair.2.unpair.1.unpair.1 - 1).unpair.1) :=
    Nat.Primrec.left.comp hpm
  have hrw' : Nat.Primrec (fun w : ℕ => (w.unpair.2.unpair.1.unpair.1 - 1).unpair.2) :=
    Nat.Primrec.right.comp hpm
  have hcall : Nat.Primrec (fun w : ℕ =>
      qc (Nat.pair (w.unpair.2.unpair.1.unpair.1 - 1).unpair.1 w.unpair.1)) :=
    hqc.comp (hi.pair hx)
  have hB : Nat.Primrec (fun w : ℕ =>
      selectFn w.unpair.2.unpair.1.unpair.2
        (isOne (qc (Nat.pair (w.unpair.2.unpair.1.unpair.1 - 1).unpair.1 w.unpair.1))) 0) :=
    primrec_selectFn hflag (primrec_isOne.comp hcall) (Nat.Primrec.const 0)
  exact (hrw'.pair hB).of_eq (fun _ => rfl)

theorem primrec_reForallChar {qc : ℕ → ℕ} (hqc : Nat.Primrec qc) :
    Nat.Primrec (fun t => reForallChar qc t.unpair.1 t.unpair.2) := by
  have hfold := primrec_foldCode (primrec_reForallStp hqc) (Nat.Primrec.const 0)
    (Nat.Primrec.left.pair (Nat.Primrec.const 1)) Nat.Primrec.right
  exact (Nat.Primrec.right.comp hfold).of_eq (fun _ => rfl)

/-- **Bounded `∀` over a coded list preserves recursive enumerability.** If `p` is r.e. then so is
`fun c => ∀ e ∈ decodeList c, p e`: the finite tuple of per-entry witnesses is packed into a single
search code `w`, and the `{0,1}` flag `reForallChar` makes the body recursively decidable. -/
theorem REPred.forall_mem_decodeList {p : ℕ → Prop} (hp : REPred p) :
    REPred (fun c => ∀ e ∈ decodeList c, p e) := by
  obtain ⟨q, hq, hqe⟩ := hp
  obtain ⟨qc, hqcp, hqcs⟩ := hq
  -- per-entry: `p e ↔ ∃ j, qc ⟨j, e⟩ = 1`
  have hpe : ∀ e, p e ↔ ∃ j, qc (Nat.pair j e) = 1 := by
    intro e; rw [hqe e]; exact exists_congr (fun j => hqcs (Nat.pair j e))
  -- membership gives an index whose `getD` recovers the element
  have hmemgetD : ∀ (l : List ℕ) (e : ℕ), e ∈ l → ∃ k, k < l.length ∧ l.getD k 0 = e := by
    intro l
    induction l with
    | nil => intro e he; cases he
    | cons a l ih =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he'
      · exact ⟨0, by simp only [List.length_cons]; omega, by rw [List.getD_cons_zero]⟩
      · obtain ⟨k, hk, hek⟩ := ih e he'
        exact ⟨k + 1, by simp only [List.length_cons]; omega, by rw [List.getD_cons_succ]; exact hek⟩
  refine ⟨fun t => reForallChar qc t.unpair.1 t.unpair.2 = 1,
    ⟨fun t => reForallChar qc t.unpair.1 t.unpair.2, primrec_reForallChar hqcp,
      fun _ => Iff.rfl⟩, fun c => ?_⟩
  simp only [unpair_pair_fst, unpair_pair_snd]
  constructor
  · intro hall
    -- build a witness list for `decodeList c`
    have hwit : ∀ (l : List ℕ), (∀ e ∈ l, ∃ j, qc (Nat.pair j e) = 1) →
        ∃ iws : List ℕ, ∀ k, k < l.length →
          qc (Nat.pair (iws.getD k 0) (l.getD k 0)) = 1 := by
      intro l
      induction l with
      | nil => intro _; exact ⟨[], fun k hk => absurd hk (Nat.not_lt_zero k)⟩
      | cons e l ih =>
        intro hh
        obtain ⟨j, hj⟩ := hh e (List.mem_cons.mpr (Or.inl rfl))
        obtain ⟨iws, hiws⟩ := ih (fun e' he' => hh e' (List.mem_cons.mpr (Or.inr he')))
        refine ⟨j :: iws, fun k hk => ?_⟩
        rcases k with _ | k'
        · rw [List.getD_cons_zero, List.getD_cons_zero]; exact hj
        · rw [List.getD_cons_succ, List.getD_cons_succ]
          exact hiws k' (by simp only [List.length_cons] at hk; omega)
    obtain ⟨iws, hiws⟩ := hwit (decodeList c) (fun e he => (hpe e).mp (hall e he))
    refine ⟨encodeList iws, (reForallChar_eq_one_iff qc _ c).mpr (fun k hk => ?_)⟩
    rw [decodeList_encodeList]; exact hiws k hk
  · rintro ⟨w, hw⟩
    rw [reForallChar_eq_one_iff] at hw
    intro e he
    obtain ⟨k, hk, hek⟩ := hmemgetD (decodeList c) e he
    rw [hpe e]
    refine ⟨(decodeList w).getD k 0, ?_⟩
    have := hw k hk
    rwa [hek] at this

/-! ### Bounded `∀` over a coded list with a parameter (for `curry`, Theorem 7.5)

`curry`'s neighbourhood relation is a bounded `∀ e ∈ decodeList c, p n e` whose body depends on a
*parameter* `n` (the `𝒟₀`-index) as well as the list entry `e`. We reduce this to
`REPred.forall_mem_decodeList` by primitively-recursively re-coding the list `decodeList c` into the
list of pairs `⟨n, e⟩` (order is irrelevant under `∀ ∈`), so the parameterised body becomes the
plain `fun s => p s.1 s.2` over the re-coded list. -/


/-! ## Choice-free primitive-recursive bitwise OR (for Example 7.8, the powerset `PN`)

Scott's Example 7.8 enumerates the finite subsets of `ℕ` by `Eₙ = {k ∣ n.testBit k}` and presents the
powerset domain `PN` with neighbourhoods `ℕ ∖ Eₙ`. The intersection of two neighbourhoods is
`(ℕ ∖ Eₙ) ∩ (ℕ ∖ Eₘ) = ℕ ∖ (Eₙ ∪ Eₘ) = ℕ ∖ E_{n ||| m}` (bitwise OR), and Scott notes that the
relation `Eₙ ∪ Eₘ = E_k` is *recursive*. The presentation therefore needs `(n, m) ↦ n ||| m` as a
**primitive-recursive** intersection function.

mathlib's `Nat.lor` is defined through `Nat.bitwise`/`binaryRec`, none of which is exposed as a
`Nat.Primrec`. We build it choice-free by *iterating* a fixed step `lorStep` (which strips the low
bit of each argument, ORs them, and accumulates with a doubling weight). The result coincides with
`Nat.lor` (`myLor_eq_lor`), so all the set-level facts can use mathlib's clean `Nat.testBit_lor`. -/


/-- `lowOr x y = (x ||| y) % 2`: both sides depend only on the low bits `x % 2`, `y % 2`. -/
theorem lowOr_eq_mod (x y : ℕ) : lowOr x y = (x ||| y) % 2 := by
  have key : ((x ||| y) % 2 = 1) ↔ (x % 2 = 1 ∨ y % 2 = 1) := by
    have hb := Nat.testBit_lor x y 0
    rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at hb
    rw [← decide_eq_decide, hb, Bool.decide_or]
  have e1 : (x ||| y) % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold lowOr
  -- explicit case split avoids feeding `omega` an `↔`/disjunction (which pulls `Classical.choice`)
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> rw [hx, hy]
  · -- x%2=0, y%2=0 : `(x|||y)%2 ≠ 1`
    have hne : (x ||| y) % 2 ≠ 1 := fun h => by rcases key.mp h with h' | h' <;> omega
    omega
  · -- x%2=0, y%2=1
    rw [key.mpr (Or.inr hy)]
  · -- x%2=1, y%2=0
    rw [key.mpr (Or.inl hx)]
  · -- x%2=1, y%2=1
    rw [key.mpr (Or.inl hx)]


/-- One recursion step for `Nat.lor` on the low bit: `x ||| y = 2 (x/2 ||| y/2) + lowOr x y`. -/
theorem lor_low_rec (x y : ℕ) : x ||| y = 2 * (x / 2 ||| y / 2) + lowOr x y := by
  have hdiv : (x ||| y) / 2 = x / 2 ||| y / 2 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [← Nat.testBit_add_one, Nat.testBit_lor, Nat.testBit_lor, Nat.testBit_add_one,
      Nat.testBit_add_one]
  have hmod := lowOr_eq_mod x y
  conv_lhs => rw [← Nat.div_add_mod (x ||| y) 2]
  rw [hdiv, hmod]

/-- **Invariant of the bitwise-OR iteration.** After `k` steps the two running arguments are
`a / 2^k`, `b / 2^k`, the weight is `2^k`, and `acc + 2^k · (a/2^k ||| b/2^k) = a ||| b`. -/
theorem lorStep_iter_spec (a b : ℕ) : ∀ k,
    (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 = a / 2 ^ k ∧
    (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 = b / 2 ^ k ∧
    (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 = 2 ^ k ∧
    (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2 +
        2 ^ k * (a / 2 ^ k ||| b / 2 ^ k) = a ||| b := by
  intro k
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply, unpair_pair_fst, unpair_pair_snd, pow_zero,
      Nat.div_one, Nat.one_mul, Nat.zero_add, true_and]
  | succ k ih =>
    obtain ⟨hA, hB, hW, hAcc⟩ := ih
    rw [Function.iterate_succ_apply']
    have hdd : a / 2 ^ (k + 1) = (a / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have hdd' : b / 2 ^ (k + 1) = (b / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    -- compute the four projections of one `lorStep`
    have p11 : (lorStep (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.1
        = (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 / 2 := by
      unfold lorStep; rw [unpair_pair_fst, unpair_pair_fst]
    have p12 : (lorStep (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.2
        = (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 / 2 := by
      unfold lorStep; rw [unpair_pair_fst, unpair_pair_snd]
    have p21 : (lorStep (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.1
        = 2 * (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 := by
      unfold lorStep; rw [unpair_pair_snd, unpair_pair_fst]
    have p22 : (lorStep (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.2
        = (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2
          + (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1
            * lowOr (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1
                (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 := by
      unfold lorStep; rw [unpair_pair_snd, unpair_pair_snd]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [p11, hA, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p12, hB, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p21, hW, ← pow_succ']
    · rw [p22, hA, hB, hW, hdd, hdd', pow_succ, ← hAcc, lor_low_rec (a / 2 ^ k) (b / 2 ^ k)]
      ring

/-- **Correctness of the iterative bitwise OR.** `myLor a b = a ||| b`. -/
theorem myLor_eq_lor (a b : ℕ) : myLor a b = a ||| b := by
  unfold myLor
  obtain ⟨_, _, _, hAcc⟩ := lorStep_iter_spec a b (a + b)
  have ha0 : a / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_right a b)))
  have hb0 : b / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_left b a)))
  rw [ha0, hb0] at hAcc
  simpa using hAcc

/-! ## Bounded quantifiers over a coded list preserving recursive *decidability*

`reForallChar`/`REPred.forall_mem_decodeList` above handle bounded `∀` over `decodeList` for *r.e.*
predicates (which need a witness search). When the body is already recursively *decidable* the story
is simpler: fold the `{0,1}` decider over the list with a Boolean `AND` (for `∀`) or `OR` (for `∃`),
no witness threading. These are exactly what Scott's Smyth power-domain equality relation
(Proposition 7.10) needs: equality of two finite unions of down-sets unfolds to
`(∀ a ∈ A, ∃ b ∈ B, …) ∧ (∀ b ∈ B, ∃ a ∈ A, …)`, a nested bounded ∀/∃ over coded lists. All
choice-free. The list is coded by the *first* argument; the *second* argument is a free parameter
threaded through the `foldCode` `params` slot. -/


theorem allListStp_eq (g : ℕ → ℕ) (acc x p : ℕ) :
    allListStp g (Nat.pair x (Nat.pair acc p)) = selectFn acc (isOne (g (Nat.pair x p))) 0 := by
  unfold allListStp; simp only [unpair_pair_fst, unpair_pair_snd]

theorem allListChar_eq (g : ℕ → ℕ) (p c : ℕ) :
    allListChar g p c
      = List.foldl (fun acc x => selectFn acc (isOne (g (Nat.pair x p))) 0) 1 (decodeList c) := by
  have hfun : (fun (acc x : ℕ) => allListStp g (Nat.pair x (Nat.pair acc p)))
      = (fun acc x => selectFn acc (isOne (g (Nat.pair x p))) 0) := by
    funext acc x; exact allListStp_eq g acc x p
  unfold allListChar; rw [foldCode_eq', hfun]

/-- Core induction for the AND-fold: starting from `acc ≤ 1`, the fold is `1` iff `acc = 1` and every
list entry passes the decider `g`. -/
theorem allList_foldl_eq_one_iff (g : ℕ → ℕ) (p : ℕ) :
    ∀ (l : List ℕ) (acc : ℕ), acc ≤ 1 →
      (List.foldl (fun acc x => selectFn acc (isOne (g (Nat.pair x p))) 0) acc l = 1 ↔
        acc = 1 ∧ ∀ x ∈ l, g (Nat.pair x p) = 1) := by
  intro l
  induction l with
  | nil => intro acc _; simp only [List.foldl_nil, List.not_mem_nil, false_implies, implies_true,
      and_true]
  | cons x l ih =>
    intro acc hacc
    rw [List.foldl_cons]
    set acc' := selectFn acc (isOne (g (Nat.pair x p))) 0 with hacc'
    have hacc'le : acc' ≤ 1 := by
      rw [hacc']
      rcases (show acc = 0 ∨ acc = 1 by omega) with h | h
      · rw [h, selectFn_zero]; exact Nat.zero_le 1
      · rw [h, selectFn_one]; exact isOne_le_one _
    rw [ih acc' hacc'le]
    constructor
    · rintro ⟨hacc'1, hrest⟩
      have hsplit : acc = 1 ∧ g (Nat.pair x p) = 1 := by
        rw [hacc'] at hacc'1
        rcases (show acc = 0 ∨ acc = 1 by omega) with h | h
        · rw [h, selectFn_zero] at hacc'1; exact absurd hacc'1 (by decide)
        · rw [h, selectFn_one, isOne_eq_one_iff] at hacc'1; exact ⟨h, hacc'1⟩
      refine ⟨hsplit.1, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hsplit.2
      · exact hrest y hy'
    · rintro ⟨hacc1, hall⟩
      have hhead : g (Nat.pair x p) = 1 := hall x (List.mem_cons.mpr (Or.inl rfl))
      refine ⟨?_, fun y hy => hall y (List.mem_cons.mpr (Or.inr hy))⟩
      rw [hacc', hacc1, selectFn_one, isOne_eq_one_iff]; exact hhead

theorem allListChar_eq_one_iff (g : ℕ → ℕ) (p c : ℕ) :
    allListChar g p c = 1 ↔ ∀ x ∈ decodeList c, g (Nat.pair x p) = 1 := by
  rw [allListChar_eq, allList_foldl_eq_one_iff g p (decodeList c) 1 (Nat.le_refl 1)]
  simp only [true_and]

theorem allListChar_le_one (g : ℕ → ℕ) (p c : ℕ) : allListChar g p c ≤ 1 := by
  have h : ∀ (l : List ℕ) (z : ℕ), z ≤ 1 →
      List.foldl (fun acc x => allListStp g (Nat.pair x (Nat.pair acc p))) z l ≤ 1 := by
    intro l
    induction l with
    | nil => intro z hz; simpa using hz
    | cons x xs ih =>
      intro z hz
      simp only [List.foldl_cons]
      apply ih
      rw [allListStp_eq]
      rcases (show z = 0 ∨ z = 1 by omega) with h0 | h1
      · rw [h0, selectFn_zero]; exact Nat.zero_le 1
      · rw [h1, selectFn_one]; exact isOne_le_one _
  unfold allListChar
  rw [foldCode_eq']
  exact h (decodeList c) 1 (le_refl 1)

theorem primrec_allListStp {g : ℕ → ℕ} (hg : Nat.Primrec g) : Nat.Primrec (allListStp g) := by
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hp : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hcall : Nat.Primrec (fun w : ℕ => isOne (g (Nat.pair w.unpair.1 w.unpair.2.unpair.2))) :=
    primrec_isOne.comp (hg.comp (hx.pair hp))
  exact (primrec_selectFn hacc hcall (Nat.Primrec.const 0)).of_eq fun _ => rfl


theorem isBinDigit_eq_one_iff (n : ℕ) : isBinDigit n = 1 ↔ n = 0 ∨ n = 1 := by
  unfold isBinDigit selectFn isOne
  match n with | 0 | 1 => simp | n + 2 => simp

theorem primrec_isBinDigit : Nat.Primrec isBinDigit := by
  have h01 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) primrec_id)
  have h12 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 2) primrec_id)
  refine (primrec_selectFn h01 (Nat.Primrec.const 1)
    (primrec_selectFn h12 (Nat.Primrec.const 1) (Nat.Primrec.const 0))).of_eq fun _ => rfl


theorem allBinDigitsChar_eq_one_iff (c : ℕ) :
    allBinDigitsChar c = 1 ↔ ∀ x ∈ decodeList c, x = 0 ∨ x = 1 := by
  unfold allBinDigitsChar
  rw [allListChar_eq_one_iff]
  simp [isBinDigit_eq_one_iff]

theorem allBinDigitsChar_le_one (c : ℕ) : allBinDigitsChar c ≤ 1 := by
  unfold allBinDigitsChar; exact allListChar_le_one _ _ _

set_option maxHeartbeats 800000 in
theorem primrec_allBinDigitsChar : Nat.Primrec allBinDigitsChar := by
  unfold allBinDigitsChar
  exact (primrec_foldCode (primrec_allListStp (primrec_isBinDigit.comp Nat.Primrec.left))
    (Nat.Primrec.const 0) (Nat.Primrec.const 1) primrec_id).of_eq fun _ => rfl

/-! ## Random access and tabulation of coded lists (for the iterate `𝒟^∞`, Exercise 7.15)

`𝒟^∞`-neighbourhoods are finitely-supported sequences of `𝒟`-neighbourhoods, coded as a list of
component indices. The presentation's relations index *positions* of the list, so we need
primitive-recursive list **indexing** `nthCode c i d = (decodeList c).getD i d` and a **tabulation**
`tabCode g p B` coding `[g⟨0,p⟩, …, g⟨B-1,p⟩]` (used for the intersection function). Both choice-free,
both built from the existing `foldCode`/`Nat.Primrec.prec` engine. -/


theorem nthStp_val (i x s r : ℕ) :
    nthStp (Nat.pair x (Nat.pair (Nat.pair s r) i))
      = Nat.pair (s + 1) (selectFn (1 - ((s - i) + (i - s))) x r) := by
  unfold nthStp; simp only [unpair_pair_fst, unpair_pair_snd]


theorem nthCode_foldl (i : ℕ) : ∀ (l : List ℕ) (s r : ℕ),
    (List.foldl (fun acc x => nthStp (Nat.pair x (Nat.pair acc i))) (Nat.pair s r) l).unpair.2
      = if i < s then r else l.getD (i - s) r := by
  intro l
  induction l with
  | nil => intro s r; simp only [List.foldl_nil, unpair_pair_snd, List.getD_nil]; split <;> rfl
  | cons x l ih =>
    intro s r
    rw [List.foldl_cons, nthStp_val, ih (s + 1) (selectFn (1 - ((s - i) + (i - s))) x r)]
    by_cases h : i = s
    · subst h
      have he : (1 : ℕ) - ((i - i) + (i - i)) = 1 := by omega
      rw [he, selectFn_one, ite_eq_right (lt_irrefl i), ite_eq_left (Nat.lt_succ_self i), Nat.sub_self,
        List.getD_cons_zero]
    · by_cases h2 : i < s
      · have he : (1 : ℕ) - ((s - i) + (i - s)) = 0 := by omega
        rw [he, selectFn_zero, ite_eq_left h2, ite_eq_left (Nat.lt_succ_of_lt h2)]
      · have he : (1 : ℕ) - ((s - i) + (i - s)) = 0 := by omega
        rw [he, selectFn_zero, ite_eq_right h2, ite_eq_right (show ¬ i < s + 1 by omega),
          show i - s = (i - (s + 1)) + 1 by omega, List.getD_cons_succ]

theorem nthCode_eq (c i d : ℕ) : nthCode c i d = (decodeList c).getD i d := by
  unfold nthCode
  rw [foldCode_eq']
  have h := nthCode_foldl i (decodeList c) 0 d
  rw [ite_eq_right (Nat.not_lt_zero i), Nat.sub_zero] at h
  exact h

theorem primrec_nthStp : Nat.Primrec nthStp := by
  have hcount : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hres : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hbit : Nat.Primrec (fun w : ℕ => 1 - ((w.unpair.2.unpair.1.unpair.1 - w.unpair.2.unpair.2)
      + (w.unpair.2.unpair.2 - w.unpair.2.unpair.1.unpair.1))) :=
    primrec_sub₂ (Nat.Primrec.const 1)
      (primrec_add₂ (primrec_sub₂ hcount hi) (primrec_sub₂ hi hcount))
  exact ((Nat.Primrec.succ.comp hcount).pair (primrec_selectFn hbit hx hres)).of_eq fun _ => rfl

/-- `nthCode` is primitive recursive in `(c, i, d)` (coded as `pair c (pair i d)`). -/
theorem primrec_nthCode : Nat.Primrec
    (fun t => nthCode t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hfold := primrec_foldCode primrec_nthStp (Nat.Primrec.left.comp Nat.Primrec.right)
    ((Nat.Primrec.const 0).pair (Nat.Primrec.right.comp Nat.Primrec.right)) Nat.Primrec.left
  exact (Nat.Primrec.right.comp hfold).of_eq fun _ => rfl


theorem tabStep_val (g : ℕ → ℕ) (a y IH : ℕ) :
    tabStep g (Nat.pair a (Nat.pair y IH))
      = Nat.pair (g (Nat.pair (a.unpair.1 - 1 - y) a.unpair.2)) IH + 1 := by
  unfold tabStep; simp only [unpair_pair_fst, unpair_pair_snd]


/-- After `K ≤ B` steps the accumulated code decodes to the indices `B-K, …, B-1`. -/
theorem decodeList_tabCode_aux (g : ℕ → ℕ) (B p : ℕ) :
    ∀ K, K ≤ B → decodeList (Nat.rec (motive := fun _ => ℕ) 0
        (fun y IH => tabStep g (Nat.pair (Nat.pair B p) (Nat.pair y IH))) K)
      = (List.range' (B - K) K).map (fun j => g (Nat.pair j p)) := by
  intro K
  induction K with
  | zero => intro _; simp [decodeList_zero]
  | succ K ih =>
    intro hK
    have hKB : K ≤ B := Nat.le_of_succ_le hK
    show decodeList (tabStep g (Nat.pair (Nat.pair B p) (Nat.pair K
      (Nat.rec (motive := fun _ => ℕ) 0
        (fun y IH => tabStep g (Nat.pair (Nat.pair B p) (Nat.pair y IH))) K)))) = _
    rw [tabStep_val]
    simp only [unpair_pair_fst, unpair_pair_snd]
    rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, ih hKB,
      show B - (K + 1) = B - 1 - K by omega, List.range'_succ, List.map_cons,
      show B - 1 - K + 1 = B - K by omega]

theorem decodeList_tabCode (g : ℕ → ℕ) (B p : ℕ) :
    decodeList (tabCode g (Nat.pair B p) B) = (List.range B).map (fun j => g (Nat.pair j p)) := by
  have h := decodeList_tabCode_aux g B p B (le_refl B)
  rw [Nat.sub_self, ← List.range_eq_range'] at h
  exact h

/-! ### Choice-free `List.getD` facts.

Mathlib's `List.getD_eq_getElem`/`List.getD_eq_default`/`getD_append`(`_right`) are proved by `grind`,
which pulls `Classical.choice`. We re-prove the slice we need by structural induction (using only the
choice-free `getD_nil`/`getD_cons_zero`/`getD_cons_succ`), so the `D^∞` presentation stays
`⊆ {propext, Quot.sound}`. -/

/-- Choice-free `getD`-as-`getElem` in range. -/
theorem getD_eq_getElem_cf {β : Type*} (l : List β) (d : β) :
    ∀ {n : ℕ} (h : n < l.length), l.getD n d = l[n] := by
  induction l with
  | nil => intro n h; exact absurd h (Nat.not_lt_zero n)
  | cons a t ih =>
    intro n h
    cases n with
    | zero => rw [List.getD_cons_zero, List.getElem_cons_zero]
    | succ m => rw [List.getD_cons_succ, List.getElem_cons_succ]; exact ih _

/-- Choice-free default-out-of-range. -/
theorem getD_eq_default_cf {β : Type*} (l : List β) (d : β) :
    ∀ {n : ℕ}, l.length ≤ n → l.getD n d = d := by
  induction l with
  | nil => intro n _; exact List.getD_nil
  | cons a t ih =>
    intro n h
    cases n with
    | zero => exact absurd h (by rw [List.length_cons]; exact Nat.not_succ_le_zero _)
    | succ m => rw [List.getD_cons_succ]; exact ih (by rw [List.length_cons] at h; omega)

/-- Choice-free `getD` of a mapped `range`. -/
theorem getD_map_range_cf {β : Type*} (h : ℕ → β) (d : β) {B i : ℕ} (hi : i < B) :
    ((List.range B).map h).getD i d = h i := by
  have hlen : ((List.range B).map h).length = B := by rw [List.length_map, List.length_range]
  rw [getD_eq_getElem_cf _ d (by rw [hlen]; exact hi), List.getElem_map, List.getElem_range]

theorem tabCode_nth_lt {g : ℕ → ℕ} {B p i : ℕ} (hi : i < B) (d : ℕ) :
    nthCode (tabCode g (Nat.pair B p) B) i d = g (Nat.pair i p) := by
  rw [nthCode_eq, decodeList_tabCode, getD_map_range_cf]; exact hi

theorem tabCode_nth_ge {g : ℕ → ℕ} {B p i : ℕ} (hi : B ≤ i) (d : ℕ) :
    nthCode (tabCode g (Nat.pair B p) B) i d = d := by
  rw [nthCode_eq, decodeList_tabCode, getD_eq_default_cf]
  rw [List.length_map, List.length_range]; exact hi

theorem primrec_tabStep {g : ℕ → ℕ} (hg : Nat.Primrec g) : Nat.Primrec (tabStep g) := by
  have hB : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have hp : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hk : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hih : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hidx : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.1 - 1 - w.unpair.2.unpair.1) :=
    primrec_sub₂ (primrec_sub₂ hB (Nat.Primrec.const 1)) hk
  exact (Nat.Primrec.succ.comp ((hg.comp (hidx.pair hp)).pair hih)).of_eq fun _ => rfl

/-- `tabCode g · ·` is primitive recursive in `(a, B)` (coded `pair a B`), whenever `g` is. -/
theorem primrec_tabCode {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (fun t => tabCode g t.unpair.1 t.unpair.2) :=
  (Nat.Primrec.prec (Nat.Primrec.const 0) (primrec_tabStep hg)).of_eq fun t => by
    simp only [Nat.unpaired]; rfl

/-! ## Course-of-values fuel recursion → joint primitive recursiveness

`decodeFuelOkChar`, `matchesBChar`, `autStateCardFuelChar` are each defined by structural
recursion on a `fuel : ℕ` parameter, where the recursive step (`decodeFuelOkCharBody`, etc.)
applies the *previous* fuel level's function `prev : ℕ → ℕ` at sub-codes of its own input `c`
(via `Nat.unpair`), not merely at `c` decremented. Each is only known `Nat.Primrec` *for a fixed
external `fuel`* (`∀ fuel, Nat.Primrec (fun c => F fuel c)`) — that is not enough once `fuel`
itself must vary with the input (as it does for `ssysActiveChar`, C9b7, where `fuel := n.unpair.2
+ 1`). Getting a genuinely joint `Nat.Primrec (fun t => F t.unpair.1 t.unpair.2)` needs
course-of-values recursion: tabulate `F fuel` at every code up to a bound as a coded list
(`tabCode`/`nthCode`), and iterate that *table transform* via `Nat.rec` on `fuel`, mirroring
`tabCode`'s own already-established proof pattern. Since `Body`'s sub-queries at code `c` are
always `≤ c` (chains of `Nat.unpair` projections), a table covering `[0, c]` is self-sufficient
throughout the whole recursion — no growing/re-tabulating needed as fuel increases. -/


/-- Tag-dispatch on `e.unpair.1 ∈ {0,1,2,3}` (else `fdef e`). -/
theorem primrec_tagCase4 {f0 f1 f2 f3 fdef : ℕ → ℕ}
    (hf0 : Nat.Primrec f0) (hf1 : Nat.Primrec f1) (hf2 : Nat.Primrec f2) (hf3 : Nat.Primrec f3)
    (hfdef : Nat.Primrec fdef) :
    Nat.Primrec (fun e =>
      let t := e.unpair.1
      selectFn (isOne (1 - t)) (f0 e)
        (selectFn (isOne (2 - t)) (f1 e)
          (selectFn (isOne (3 - t)) (f2 e)
            (selectFn (isOne (4 - t)) (f3 e) (fdef e))))) := by
  have ht : Nat.Primrec (fun e => e.unpair.1) := Nat.Primrec.left
  have h01 : Nat.Primrec (fun e => isOne (1 - e.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) ht)
  have h12 : Nat.Primrec (fun e => isOne (2 - e.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 2) ht)
  have h23 : Nat.Primrec (fun e => isOne (3 - e.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 3) ht)
  have h34 : Nat.Primrec (fun e => isOne (4 - e.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 4) ht)
  refine (primrec_selectFn h01 hf0
    (primrec_selectFn h12 hf1
      (primrec_selectFn h23 hf2
        (primrec_selectFn h34 hf3 hfdef)))).of_eq fun e => rfl

/-! ## Exercise 7.22 C9b1 — fuel-bounded `SExpr` decode ok flag

Mirrors tag dispatch on `c.unpair.1 ∈ {0,1,2,3}`; at `fuel + 1` recurses at `fuel` on sub-codes
for `.cat`/`.cap`. Shallow link **7.22i(b)1(d–e)** uses dispatch lemmas from **7.22i(b)1(c)**. -/


theorem mulBit_eq_one_iff (a b : ℕ) : mulBit a b = 1 ↔ a = 1 ∧ b = 1 := by
  simp [mulBit]

theorem mulBit_le_one {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : mulBit a b ≤ 1 := by
  unfold mulBit
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> simp

theorem primrec_mulBit : Nat.Primrec (fun t => mulBit t.unpair.1 t.unpair.2) :=
  primrec_mul₂ Nat.Primrec.left Nat.Primrec.right


/-- Tag-dispatch form of `decodeFuelOkCharBody` (**7.22i(b)1(c)**). -/
theorem decodeFuelOkCharBody_eq (prev : ℕ → ℕ) (c : ℕ) :
    decodeFuelOkCharBody prev c =
      match c.unpair.1 with
      | 0 => selectFn (isOne (1 - c.unpair.2)) 1 0
      | 1 => allBinDigitsChar c.unpair.2
      | 2 | 3 => mulBit (prev c.unpair.2.unpair.1) (prev c.unpair.2.unpair.2)
      | _ => 0 := by
  unfold decodeFuelOkCharBody mulBit
  match tag : c.unpair.1 with
  | 0 =>
    have h10 : (1 - 0 : ℕ) = 1 := rfl
    simp only [h10, isOne_one, selectFn_one]
  | 1 =>
    have h01 : (1 - 1 : ℕ) = 0 := rfl
    have h12 : (2 - 1 : ℕ) = 1 := rfl
    simp only [h01, h12, isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | 2 =>
    have h01 : (1 - 2 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12 : (2 - 2 : ℕ) = 0 := rfl
    have h23 : (3 - 2 : ℕ) = 1 := rfl
    simp only [h01, h23, isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | 3 =>
    have h01 : (1 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12 : (2 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h23 : (3 - 3 : ℕ) = 0 := rfl
    have h34 : (4 - 3 : ℕ) = 1 := rfl
    simp only [h01, h34, isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | t + 4 =>
    have hne1 : isOne (1 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    have hne2 : isOne (2 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    have hne3 : isOne (3 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    have hne4 : isOne (4 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    simp only [hne1, hne2, hne3, hne4, selectFn_zero]


theorem primrec_decodeFuelOkCharBody {prev : ℕ → ℕ} (hprev : Nat.Primrec prev) :
    Nat.Primrec (fun c => decodeFuelOkCharBody prev c) := by
  unfold decodeFuelOkCharBody
  have hleft : Nat.Primrec (fun c => prev c.unpair.2.unpair.1) :=
    (hprev.comp (Nat.Primrec.left.comp Nat.Primrec.right)).of_eq fun c => by
      simp only
  have hright : Nat.Primrec (fun c => prev c.unpair.2.unpair.2) :=
    (hprev.comp (Nat.Primrec.right.comp Nat.Primrec.right)).of_eq fun c => by
      simp only
  have hsub : Nat.Primrec (fun c => mulBit (prev c.unpair.2.unpair.1) (prev c.unpair.2.unpair.2)) :=
    primrec_mul₂ hleft hright
  have hf0 : Nat.Primrec (fun c => selectFn (isOne (1 - c.unpair.2)) 1 0) :=
    primrec_selectFn
      (primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) Nat.Primrec.right))
      (Nat.Primrec.const 1) (Nat.Primrec.const 0)
  have hf1 : Nat.Primrec (fun c => allBinDigitsChar c.unpair.2) :=
    primrec_allBinDigitsChar.comp Nat.Primrec.right
  exact primrec_tagCase4 hf0 hf1 hsub hsub (Nat.Primrec.const 0)

/-! ### `decodeFuelOkChar` jointly primitive recursive in `(fuel, code)`

Instantiates the generic course-of-values machinery above: `decodeFuelOkCharBody`'s only
recursive calls are at `c.unpair.2.unpair.1`/`c.unpair.2.unpair.2`, both `≤ c`
(`unpair_left_le`/`unpair_snd_le`), so `hlocal` holds. -/

theorem decodeFuelOkCharBody_local (f g : ℕ → ℕ) (c : ℕ) (h : ∀ c' ≤ c, f c' = g c') :
    decodeFuelOkCharBody f c = decodeFuelOkCharBody g c := by
  rw [decodeFuelOkCharBody_eq, decodeFuelOkCharBody_eq]
  have h1 : c.unpair.2.unpair.1 ≤ c := le_trans (unpair_left_le c.unpair.2) (unpair_snd_le c)
  have h2 : c.unpair.2.unpair.2 ≤ c := le_trans (unpair_snd_le c.unpair.2) (unpair_snd_le c)
  rw [h _ h1, h _ h2]


/-! ## Exercise 7.22 C9b2 — coded list length

`listLenChar c` = `(decodeList c).length`, via a `foldCode` counter (**7.22i(b)2**). -/


theorem listLenStp_eq (acc x p : ℕ) :
    listLenStp (Nat.pair x (Nat.pair acc p)) = acc + 1 := by
  unfold listLenStp; simp only [unpair_pair_fst, unpair_pair_snd]


theorem listLenChar_eq (c : ℕ) : listLenChar c = (decodeList c).length := by
  have hfun : (fun acc x => listLenStp (Nat.pair x (Nat.pair acc 0))) = fun acc _ => acc + 1 := by
    funext acc x; simp [listLenStp_eq]
  have hfold : ∀ (k : ℕ) (l : List ℕ),
      List.foldl (fun acc _ => acc + 1) k l = k + l.length := by
    intro k l
    induction l generalizing k with
    | nil => simp
    | cons _ xs ih => simp [List.foldl_cons, ih, List.length_cons]; omega
  unfold listLenChar
  rw [foldCode_eq', hfun]
  simp [hfold]

theorem primrec_listLenStp : Nat.Primrec listLenStp :=
  primrec_add₂ (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)

theorem primrec_listLenChar : Nat.Primrec listLenChar := by
  unfold listLenChar
  exact (primrec_foldCode primrec_listLenStp (Nat.Primrec.const 0) (Nat.Primrec.const 0)
    primrec_id).of_eq fun _ => rfl

/-! ## Exercise 7.22 C9b3 — coded list equality

Synchronized `foldCode` over `c1` threading remainder-code of `c2` (**7.22i(b)3**). No witness
search — decidable elementwise equality only. -/


theorem natEqChar_le_one (a b : ℕ) : natEqChar a b ≤ 1 := by unfold natEqChar; omega

theorem natEqChar_eq_zero_or_one (a b : ℕ) : natEqChar a b = 0 ∨ natEqChar a b = 1 := by
  unfold natEqChar; omega

theorem primrec_natEqChar : Nat.Primrec (fun t => natEqChar t.unpair.1 t.unpair.2) :=
  (primrec_sub₂ (Nat.Primrec.const 1)
    (primrec_add₂ (primrec_sub₂ Nat.Primrec.left Nat.Primrec.right)
      (primrec_sub₂ Nat.Primrec.right Nat.Primrec.left))).of_eq fun _ => rfl


theorem listEqStp_acc (flag rem x : ℕ) :
    listEqStp (Nat.pair x (Nat.pair (Nat.pair flag rem) 0)) =
      selectFn (isZero rem) (Nat.pair 0 0)
        (Nat.pair (selectFn flag (natEqChar x ((rem - 1).unpair.1)) 0) ((rem - 1).unpair.2)) := by
  unfold listEqStp listEqStpNonzero
  simp only [unpair_pair_fst, unpair_pair_snd]


theorem decodeList_eq_nil_iff (c : ℕ) : decodeList c = [] ↔ c = 0 := by
  constructor
  · intro h
    have := congrArg encodeList h
    rwa [encodeList, encodeList_decodeList] at this
  · intro hc; simp [hc, decodeList_zero]

private theorem selectFn_eq_one_iff_zero {a b : ℕ} (ha : a = 0 ∨ a = 1) :
    selectFn a b 0 = 1 ↔ a = 1 ∧ b = 1 := by
  rcases ha with ha | ha <;> simp [selectFn, ha]

private theorem listEqStep_zero (flag x : ℕ) :
    listEqStep (Nat.pair flag 0) x = Nat.pair 0 0 := by
  simp [listEqStep, listEqStp_acc, isZero, min]

private theorem listEqStep_succ (flag x m : ℕ) :
    listEqStep (Nat.pair flag (m + 1)) x =
      Nat.pair (selectFn flag (natEqChar x m.unpair.1) 0) m.unpair.2 := by
  unfold listEqStep listEqStp listEqStpNonzero
  simp only [unpair_pair_fst, unpair_pair_snd]
  have hzero : isZero (m + 1) = 0 := by
    unfold isZero; simp
  rw [hzero, selectFn_zero, Nat.add_sub_cancel]

private theorem listEq_foldl_zero (flag x : ℕ) (xs : List ℕ) :
    (List.foldl listEqStep (Nat.pair flag 0) (x :: xs)).unpair.1 = 0 := by
  rw [List.foldl_cons, listEqStep_zero]
  induction xs with
  | nil => simp [List.foldl_nil]
  | cons y ys ih =>
    rw [List.foldl_cons, listEqStep_zero, ih]

private theorem listEq_foldl_end_iff (l1 : List ℕ) (flag rem : ℕ) (hflag : flag = 0 ∨ flag = 1) :
    (let r := List.foldl listEqStep (Nat.pair flag rem) l1
     r.unpair.1 = 1 ∧ isZero r.unpair.2 = 1) ↔
      flag = 1 ∧ l1 = decodeList rem := by
  induction l1 generalizing flag rem with
  | nil =>
    simp only [List.foldl_nil, unpair_pair_fst, unpair_pair_snd]
    constructor
    · intro ⟨hflag', hrem0⟩
      have hrem0' : rem = 0 := (isZero_eq_one_iff rem).1 hrem0
      exact ⟨hflag', ((decodeList_eq_nil_iff rem).2 hrem0').symm⟩
    · intro ⟨hflag', heq⟩
      exact ⟨hflag', (isZero_eq_one_iff rem).2 ((decodeList_eq_nil_iff rem).1 heq.symm)⟩
  | cons x xs ih =>
    by_cases hrem : rem = 0
    · subst hrem
      simp only [decodeList_zero]
      constructor
      · intro ⟨h1, _⟩
        have h0 : (let r := List.foldl listEqStep (Nat.pair flag 0) (x :: xs); r.unpair.1) = 0 := by
          show (List.foldl listEqStep (Nat.pair flag 0) (x :: xs)).unpair.1 = 0
          exact listEq_foldl_zero flag x xs
        rw [h0] at h1
        exact absurd h1 (by decide)
      · intro h
        cases h.2
    · rcases rem with _ | m
      · omega
      · set acc' := selectFn flag (natEqChar x m.unpair.1) 0 with hacc'
        have hacc01 : acc' = 0 ∨ acc' = 1 := by
          rcases hflag with h | h
          · left; rw [hacc', h, selectFn_zero]
          · have hz := natEqChar_eq_zero_or_one x m.unpair.1
            rw [hacc', h, selectFn_one]
            rcases hz with hz0 | hz1
            · exact Or.inl hz0
            · exact Or.inr hz1
        rw [List.foldl_cons, listEqStep_succ, ih acc' m.unpair.2 hacc01, decodeList_succ]
        constructor
        · intro ⟨hacc'1, hxs⟩
          have hsel : selectFn flag (natEqChar x m.unpair.1) 0 = 1 := hacc'.trans hacc'1
          rcases (selectFn_eq_one_iff_zero hflag).1 hsel with ⟨hflag1, hxeq⟩
          rw [natEqChar_eq_one_iff] at hxeq
          exact ⟨hflag1, by rw [hxeq, hxs]⟩
        · intro ⟨hflag1, heq⟩
          rcases List.cons.inj heq with ⟨hx, hxs⟩
          refine ⟨hacc'.trans ((selectFn_eq_one_iff_zero hflag).2 ⟨hflag1, by
            rw [natEqChar_eq_one_iff, hx]⟩), hxs⟩

theorem listEqChar_eq_one_iff (c1 c2 : ℕ) :
    listEqChar c1 c2 = 1 ↔ decodeList c1 = decodeList c2 := by
  unfold listEqChar
  rw [foldCode_eq', show (fun acc x => listEqStp (Nat.pair x (Nat.pair acc 0))) = listEqStep from rfl,
    mulBit_eq_one_iff]
  exact (listEq_foldl_end_iff (decodeList c1) 1 c2 (Or.inr rfl)).trans (by simp)

private theorem listEq_foldl_flag_le_one : ∀ (l : List ℕ) (z : ℕ), z.unpair.1 ≤ 1 →
    (List.foldl listEqStep z l).unpair.1 ≤ 1 := by
  intro l
  induction l with
  | nil => intro z hz; exact hz
  | cons x xs ih =>
    intro z hz
    simp only [List.foldl_cons]
    apply ih
    show (listEqStp (Nat.pair x (Nat.pair z 0))).unpair.1 ≤ 1
    have hkey := listEqStp_acc z.unpair.1 z.unpair.2 x
    rw [Nat.pair_unpair] at hkey
    rw [hkey]
    rcases (show isZero z.unpair.2 = 0 ∨ isZero z.unpair.2 = 1 from by
      have := isZero_le_one z.unpair.2; omega) with h0 | h1
    · rw [h0, selectFn_zero, unpair_pair_fst]
      rcases (show z.unpair.1 = 0 ∨ z.unpair.1 = 1 from by omega) with hf0 | hf1
      · rw [hf0, selectFn_zero]; exact Nat.zero_le 1
      · rw [hf1, selectFn_one]
        have := natEqChar_le_one x (z.unpair.2 - 1).unpair.1
        omega
    · rw [h1, selectFn_one, unpair_pair_fst]; exact Nat.zero_le 1

theorem listEqChar_le_one (c1 c2 : ℕ) : listEqChar c1 c2 ≤ 1 := by
  unfold listEqChar
  rw [foldCode_eq', show (fun acc x => listEqStp (Nat.pair x (Nat.pair acc 0))) = listEqStep from rfl]
  exact mulBit_le_one
    (listEq_foldl_flag_le_one (decodeList c1) (Nat.pair 1 c2) (by simp))
    (isZero_le_one _)

set_option maxHeartbeats 800000 in
theorem primrec_listEqStpNonzero : Nat.Primrec listEqStpNonzero := by
  have hflag := Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hrem := Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hhead := Nat.Primrec.left
  have hrem1 := primrec_sub₂ hrem (Nat.Primrec.const 1)
  have hcmp := primrec_natEqChar.comp (hhead.pair (Nat.Primrec.left.comp hrem1))
  have htail := Nat.Primrec.right.comp hrem1
  exact (Nat.Primrec.pair (primrec_selectFn hflag hcmp (Nat.Primrec.const 0)) htail).of_eq fun w => by
    simp [listEqStpNonzero, selectFn]

set_option maxHeartbeats 800000 in
theorem primrec_listEqStp : Nat.Primrec listEqStp := by
  have hrem := Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hzero := Nat.Primrec.pair (Nat.Primrec.const 0) (Nat.Primrec.const 0)
  exact (primrec_selectFn (primrec_isZero.comp hrem) hzero primrec_listEqStpNonzero).of_eq fun w => by
    simp [listEqStp, selectFn, isZero, min]

theorem primrec_listEqChar : Nat.Primrec (fun t => listEqChar t.unpair.1 t.unpair.2) := by
  have hfold := primrec_foldCode primrec_listEqStp (Nat.Primrec.const 0)
    (Nat.Primrec.pair (Nat.Primrec.const 1) Nat.Primrec.right) Nat.Primrec.left
  have hflag : Nat.Primrec (fun t =>
      (foldCode listEqStp 0 (Nat.pair 1 t.unpair.2) t.unpair.1).unpair.1) :=
    Nat.Primrec.left.comp hfold
  have hrem : Nat.Primrec (fun t =>
      (foldCode listEqStp 0 (Nat.pair 1 t.unpair.2) t.unpair.1).unpair.2) :=
    Nat.Primrec.right.comp hfold
  exact (primrec_mulBit.comp (hflag.pair (primrec_isZero.comp hrem))).of_eq fun t => by
    simp [listEqChar]

/-! ## Exercise 7.22 C9b4 — coded list append / take / drop

Built via `tabCode` + `nthCode`/`listLenChar` (no snoc/reverse fold). Correctness goes through
`tabCode_nth_lt`/`tabCode_nth_ge` + `nthCode_eq` only. -/


/-- Two lists agree when every `getD` index does. (Choice-free: `by_contra`/`Classical.choice` is
avoided by case-splitting on `Nat.lt_trichotomy` — a decidable fact — instead.) -/
theorem list_eq_of_getD {l1 l2 : List ℕ} (h : ∀ i d, l1.getD i d = l2.getD i d) : l1 = l2 := by
  have hlen : l1.length = l2.length := by
    rcases Nat.lt_trichotomy l1.length l2.length with hlt | heq | hgt
    · have h1 := h l1.length 1
      have h2 := h l1.length 2
      rw [getD_eq_default_cf l1 _ (Nat.le_refl _), getD_eq_getElem_cf l2 _ (by omega)] at h1 h2
      omega
    · exact heq
    · have h1 := h l2.length 1
      have h2 := h l2.length 2
      rw [getD_eq_getElem_cf l1 _ (by omega), getD_eq_default_cf l2 _ (Nat.le_refl _)] at h1 h2
      omega
  apply List.ext_getElem hlen
  intro i hi _
  have hi' : i < l2.length := by rw [← hlen]; exact hi
  rw [← getD_eq_getElem_cf l1 0 hi, ← getD_eq_getElem_cf l2 0 hi', h i 0]

theorem getD_take_cf (l : List ℕ) (n i d : ℕ) (hi : i < (l.take n).length) :
    (l.take n).getD i d = l.getD i d := by
  have hlen : i < l.length := by
    rw [List.length_take] at hi
    exact Nat.lt_of_lt_of_le hi (Nat.min_le_right n l.length)
  rw [getD_eq_getElem_cf (l.take n) d hi, getD_eq_getElem_cf l d hlen, List.getElem_take]

theorem getD_drop_cf (l : List ℕ) (n i d : ℕ) (hi : i < (l.drop n).length) :
    (l.drop n).getD i d = l.getD (i + n) d := by
  induction n generalizing l i d with
  | zero =>
    simp [List.drop_zero] at hi ⊢
  | succ n ih =>
    cases l with
    | nil => simp [List.drop, List.length_nil] at hi
    | cons a tl =>
      cases i with
      | zero =>
        simp [List.drop]
      | succ i =>
        simp only [List.drop]
        exact ih tl (i + 1) d (by simpa [List.length_drop] using hi)

private theorem isZero_succ_sub_len1 (i len1 : ℕ) :
    isZero ((i + 1) - len1) = 1 ↔ i < len1 := by
  unfold isZero
  constructor
  · intro h
    by_contra hge
    have hpos : 0 < (i + 1) - len1 := Nat.sub_pos_of_lt (Nat.lt_succ_of_le (Nat.le_of_not_gt hge))
    have hmin : min ((i + 1) - len1) 1 = 1 := Nat.min_eq_right (Nat.succ_le_iff.mpr hpos)
    omega
  · intro hlt
    have : (i + 1) - len1 = 0 := Nat.sub_eq_zero_iff_le.mpr (Nat.succ_le_iff.mpr hlt)
    simp [this, min]

private theorem isZero_succ_sub_len1_zero (i len1 : ℕ) (hge : len1 ≤ i) :
    isZero ((i + 1) - len1) = 0 := by
  unfold isZero
  have hpos : 0 < (i + 1) - len1 := Nat.sub_pos_of_lt (Nat.lt_succ_of_le hge)
  have hmin : min ((i + 1) - len1) 1 = 1 := Nat.min_eq_right (Nat.succ_le_iff.mpr hpos)
  simp [hmin]

theorem appendListTabFn_eq (c1 c2 len1 i : ℕ) :
    appendListTabFn (Nat.pair i (Nat.pair c1 (Nat.pair c2 len1))) =
      if i < len1 then
        (decodeList c1).getD i 0
      else
        (decodeList c2).getD (i - len1) 0 := by
  unfold appendListTabFn
  simp only [unpair_pair_fst, unpair_pair_snd]
  by_cases hlt : i < len1
  · rw [ite_eq_left hlt, (isZero_succ_sub_len1 i len1).2 hlt, selectFn_one, nthCode_eq]
  · rw [ite_eq_right hlt, isZero_succ_sub_len1_zero i len1 (Nat.le_of_not_gt hlt), selectFn_zero,
      nthCode_eq]

theorem takeCode_eq (n c : ℕ) :
    decodeList (takeCode n c) = (decodeList c).take n := by
  unfold takeCode
  rw [decodeList_tabCode, listLenChar_eq c]
  apply list_eq_of_getD
  intro i d
  by_cases hi : i < Nat.min n (decodeList c).length
  · have hic : i < (decodeList c).length := Nat.lt_of_lt_of_le hi (Nat.min_le_right n _)
    rw [getD_map_range_cf (fun j => takeListTabFn (Nat.pair j (Nat.pair n c))) d hi,
      show takeListTabFn (Nat.pair i (Nat.pair n c)) = (decodeList c).getD i d by
        have hc : (Nat.pair i (Nat.pair n c)).unpair.2.unpair.2 = c := by simp
        have hi' : (Nat.pair i (Nat.pair n c)).unpair.1 = i := by simp
        rw [takeListTabFn, hc, hi', nthCode_eq,
          show (decodeList c).getD i 0 = (decodeList c).getD i d from by
            rw [getD_eq_getElem_cf _ 0 hic, getD_eq_getElem_cf _ d hic]],
      getD_take_cf (decodeList c) n i d (by rwa [List.length_take])]
  · have hge : Nat.min n (decodeList c).length ≤ i := Nat.le_of_not_gt hi
    rw [getD_eq_default_cf _ d (by rw [List.length_map, List.length_range]; exact hge),
      getD_eq_default_cf _ d (by rw [List.length_take]; exact hge)]

theorem dropCode_eq (n c : ℕ) :
    decodeList (dropCode n c) = (decodeList c).drop n := by
  unfold dropCode
  rw [decodeList_tabCode, listLenChar_eq c]
  apply list_eq_of_getD
  intro i d
  by_cases hi : i < (decodeList c).length - n
  · have hic : i + n < (decodeList c).length := Nat.add_lt_of_lt_sub hi
    rw [getD_map_range_cf (fun j => dropListTabFn (Nat.pair j (Nat.pair n c))) d hi,
      show dropListTabFn (Nat.pair i (Nat.pair n c)) = (decodeList c).getD (i + n) d by
        have hc : (Nat.pair i (Nat.pair n c)).unpair.2.unpair.2 = c := by simp
        have hn : (Nat.pair i (Nat.pair n c)).unpair.2.unpair.1 = n := by simp
        have hi' : (Nat.pair i (Nat.pair n c)).unpair.1 = i := by simp
        rw [dropListTabFn, hi', hn, hc, nthCode_eq,
          show (decodeList c).getD (i + n) 0 = (decodeList c).getD (i + n) d from by
            rw [getD_eq_getElem_cf _ 0 hic, getD_eq_getElem_cf _ d hic]],
      getD_drop_cf (decodeList c) n i d (by rw [List.length_drop]; exact hi)]
  · have hge : (decodeList c).length - n ≤ i := Nat.le_of_not_gt hi
    rw [getD_eq_default_cf _ d (by rw [List.length_map, List.length_range]; exact hge),
      getD_eq_default_cf _ d (by rw [List.length_drop]; exact hge)]

/-- Taking a prefix never increases the Gödel code (`Nat.pair`'s monotonicity in the second
argument, chained through `encodeList`'s recursive `pair`). -/
theorem encodeList_take_le (l : List ℕ) : ∀ n, encodeList (l.take n) ≤ encodeList l := by
  induction l with
  | nil => intro n; simp [encodeList]
  | cons a l ih =>
    intro n
    cases n with
    | zero => simp [encodeList]
    | succ n =>
      show encodeList (a :: l.take n) ≤ encodeList (a :: l)
      simp only [encodeList]
      exact Nat.add_le_add_right (pair_le_pair_right' a (ih n)) 1

/-- Dropping a suffix never increases the Gödel code. -/
theorem encodeList_drop_le (l : List ℕ) : ∀ n, encodeList (l.drop n) ≤ encodeList l := by
  induction l with
  | nil => intro n; simp [encodeList]
  | cons a l ih =>
    intro n
    cases n with
    | zero => simp [encodeList]
    | succ n =>
      show encodeList (l.drop n) ≤ encodeList (a :: l)
      calc encodeList (l.drop n) ≤ encodeList l := ih n
        _ ≤ Nat.pair a (encodeList l) := le_pair_right a (encodeList l)
        _ ≤ Nat.pair a (encodeList l) + 1 := Nat.le_succ _

theorem takeCode_le (n c : ℕ) : takeCode n c ≤ c := by
  have h1 : takeCode n c = encodeList ((decodeList c).take n) := by
    rw [← takeCode_eq, encodeList_decodeList]
  rw [h1]
  exact le_trans (encodeList_take_le _ n) (le_of_eq (encodeList_decodeList c))

theorem dropCode_le (n c : ℕ) : dropCode n c ≤ c := by
  have h1 : dropCode n c = encodeList ((decodeList c).drop n) := by
    rw [← dropCode_eq, encodeList_decodeList]
  rw [h1]
  exact le_trans (encodeList_drop_le _ n) (le_of_eq (encodeList_decodeList c))

theorem primrec_takeListTabFn : Nat.Primrec takeListTabFn :=
  (primrec_nthCode.comp
    ((Nat.Primrec.right.comp Nat.Primrec.right).pair
      (Nat.Primrec.left.pair (Nat.Primrec.const 0)))).of_eq fun w => by
    simp [takeListTabFn]

theorem primrec_min {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => Nat.min (f n) (g n)) :=
  (primrec_selectFn (primrec_le hf hg) hf hg).of_eq fun n => by
    unfold selectFn isZero Nat.min
    by_cases h : f n ≤ g n
    · simp [Nat.sub_eq_zero_iff_le.mpr h, Nat.min_eq_left h]
    · have hlt : g n < f n := Nat.lt_of_not_ge h
      have hpos : 0 < f n - g n := Nat.sub_pos_of_lt hlt
      have hmin : min (f n - g n) 1 = 1 := Nat.min_eq_right (Nat.succ_le_iff.mpr hpos)
      simp [hmin, Nat.min_eq_right (Nat.le_of_lt hlt)]

theorem primrec_takeCode : Nat.Primrec (fun t => takeCode t.unpair.1 t.unpair.2) := by
  have hn := Nat.Primrec.left
  have hc := Nat.Primrec.right
  have hlen := primrec_listLenChar.comp hc
  have hB := primrec_min hn hlen
  have hp := hn.pair hc
  have hr := (hB.pair hp).pair hB
  refine ((primrec_tabCode primrec_takeListTabFn).comp hr).of_eq fun t => by
    simp [takeCode]

theorem primrec_dropListTabFn : Nat.Primrec dropListTabFn :=
  (primrec_nthCode.comp
    ((Nat.Primrec.right.comp Nat.Primrec.right).pair
      (Nat.Primrec.pair (primrec_add₂ Nat.Primrec.left (Nat.Primrec.left.comp Nat.Primrec.right))
        (Nat.Primrec.const 0)))).of_eq fun w => by
    simp [dropListTabFn]

theorem primrec_dropCode : Nat.Primrec (fun t => dropCode t.unpair.1 t.unpair.2) := by
  have hn := Nat.Primrec.left
  have hc := Nat.Primrec.right
  have hlen := primrec_listLenChar.comp hc
  have hB := primrec_sub₂ hlen hn
  have hp := hn.pair hc
  have hr := (hB.pair hp).pair hB
  refine ((primrec_tabCode primrec_dropListTabFn).comp hr).of_eq fun t => by
    simp [dropCode]

/-! ## Exercise 7.22 C9b5 — `autStateCardFuelChar`, `matchesBChar`

Fuel-bounded numeric mirrors of `autStateCard` / `matchesB` with tag dispatch like
`decodeFuelOkCharBody`. Gödel coding matches `SExpr.encode` in `Exercise722Presentation.lean`
(tags `0..3`, payloads at `c.unpair.2` / nested pairs). -/

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722


private theorem c9b5_decodeList_encodeListBool (σ : List Bool) :
    decodeList (c9b5_encodeListBool σ) = σ.map c9b5_boolNat := by
  simp [c9b5_encodeListBool, decodeList_encodeList]

private theorem c9b5_boolNat_injective : Function.Injective c9b5_boolNat := by
  intro b c h
  cases b <;> cases c <;> first | rfl | simp [c9b5_boolNat] at h

private theorem c9b5_decodeList_injective {c1 c2 : ℕ} (h : decodeList c1 = decodeList c2) : c1 = c2 := by
  have := congrArg encodeList h
  rwa [encodeList_decodeList, encodeList_decodeList] at this

private theorem c9b5_map_boolNat_eq_iff (w σ : List Bool) :
    w.map c9b5_boolNat = σ.map c9b5_boolNat ↔ w = σ := by
  constructor
  · intro h
    revert σ
    induction w with
    | nil =>
      intro σ h
      cases σ with
      | nil => rfl
      | cons _ _ => simp at h
    | cons b w ih =>
      intro σ h
      cases σ with
      | nil => simp at h
      | cons c σ =>
        simp only [List.map_cons] at h
        obtain ⟨hb, ht⟩ := List.cons.inj h
        have hb' : b = c := by
          cases b <;> cases c <;> first | rfl | simp [c9b5_boolNat] at hb
        exact hb' ▸ congrArg (List.cons c) (ih σ ht)
  · intro h; rw [h]

private theorem c9b5_takeCode_encodeListBool (w : List Bool) (i : ℕ) :
    takeCode i (c9b5_encodeListBool w) = c9b5_encodeListBool (w.take i) := by
  apply c9b5_decodeList_injective
  rw [takeCode_eq, c9b5_decodeList_encodeListBool, ← List.map_take]
  rw [c9b5_decodeList_encodeListBool (σ := w.take i)]

private theorem c9b5_dropCode_encodeListBool (w : List Bool) (i : ℕ) :
    dropCode i (c9b5_encodeListBool w) = c9b5_encodeListBool (w.drop i) := by
  apply c9b5_decodeList_injective
  rw [dropCode_eq, c9b5_decodeList_encodeListBool, ← List.map_drop]
  rw [c9b5_decodeList_encodeListBool (σ := w.drop i)]

private theorem c9b5_listEqChar_encodeListBool (w σ : List Bool) :
    listEqChar (c9b5_encodeListBool w) (c9b5_encodeListBool σ) = 1 ↔ w = σ := by
  simp only [listEqChar_eq_one_iff, c9b5_decodeList_encodeListBool, c9b5_map_boolNat_eq_iff]


theorem autStateCardFuelCharBody_eq (prev : ℕ → ℕ) (c : ℕ) :
    autStateCardFuelCharBody prev c =
      match c.unpair.1 with
      | 0 => 1
      | 1 => listLenChar c.unpair.2 + 2
      | 2 => prev c.unpair.2.unpair.1 + prev c.unpair.2.unpair.2
      | 3 => prev c.unpair.2.unpair.1 * prev c.unpair.2.unpair.2
      | _ => 0 := by
  unfold autStateCardFuelCharBody
  match tag : c.unpair.1 with
  | 0 =>
    have h10 : (1 - 0 : ℕ) = 1 := rfl
    simp only [h10, isOne_one, selectFn_one]
  | 1 =>
    have h01 : (1 - 1 : ℕ) = 0 := rfl
    have h12 : (2 - 1 : ℕ) = 1 := rfl
    simp only [h01, h12, isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | 2 =>
    have h01 : (1 - 2 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12 : (2 - 2 : ℕ) = 0 := rfl
    have h23 : (3 - 2 : ℕ) = 1 := rfl
    simp only [h01, h23, isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | 3 =>
    have h01 : (1 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12 : (2 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h23 : (3 - 3 : ℕ) = 0 := rfl
    have h34 : (4 - 3 : ℕ) = 1 := rfl
    simp only [h01, h34, isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | t + 4 =>
    have hne1 : isOne (1 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    have hne2 : isOne (2 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    have hne3 : isOne (3 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    have hne4 : isOne (4 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    simp only [hne1, hne2, hne3, hne4, selectFn_zero]


theorem autStateCardFuelChar_eq_autStateCard {fuel : ℕ} {e : SExpr}
    (h : c9b5_sexprDepth e ≤ fuel) :
    autStateCardFuelChar fuel (c9b5_sexprGodelEncode e) = autStateCard e := by
  induction e generalizing fuel with
  | sigma =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel =>
      simp [autStateCardFuelChar, autStateCardFuelCharBody_eq, c9b5_sexprGodelEncode, autStateCard]
  | single σ =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel =>
      simp [autStateCardFuelChar, autStateCardFuelCharBody_eq, c9b5_sexprGodelEncode, autStateCard,
        listLenChar_eq, c9b5_decodeList_encodeListBool, List.length_map]
  | cat a b iha ihb =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel =>
      have ha : c9b5_sexprDepth a ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      have hb : c9b5_sexprDepth b ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      simp [autStateCardFuelChar, autStateCardFuelCharBody_eq, c9b5_sexprGodelEncode, autStateCard,
        iha ha, ihb hb]
  | cap a b iha ihb =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel =>
      have ha : c9b5_sexprDepth a ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      have hb : c9b5_sexprDepth b ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      simp [autStateCardFuelChar, autStateCardFuelCharBody_eq, c9b5_sexprGodelEncode, autStateCard,
        iha ha, ihb hb]

theorem primrec_autStateCardFuelCharBody {prev : ℕ → ℕ} (hprev : Nat.Primrec prev) :
    Nat.Primrec (fun c => autStateCardFuelCharBody prev c) := by
  unfold autStateCardFuelCharBody
  have hleft : Nat.Primrec (fun c => prev c.unpair.2.unpair.1) :=
    (hprev.comp (Nat.Primrec.left.comp Nat.Primrec.right)).of_eq fun c => by
      simp only
  have hright : Nat.Primrec (fun c => prev c.unpair.2.unpair.2) :=
    (hprev.comp (Nat.Primrec.right.comp Nat.Primrec.right)).of_eq fun c => by
      simp only
  have hadd := primrec_add₂ hleft hright
  have hmul := primrec_mul₂ hleft hright
  have hf1 := primrec_add₂ (primrec_listLenChar.comp Nat.Primrec.right) (Nat.Primrec.const 2)
  exact primrec_tagCase4 (Nat.Primrec.const 1) hf1 hadd hmul (Nat.Primrec.const 0)

/-! ### `autStateCardFuelChar` jointly primitive recursive in `(fuel, code)`

Same course-of-values instantiation as `decodeFuelOkChar` above: `autStateCardFuelCharBody`'s only
recursive calls are at `c.unpair.2.unpair.1`/`c.unpair.2.unpair.2`, both `≤ c`. -/

theorem autStateCardFuelCharBody_local (f g : ℕ → ℕ) (c : ℕ) (h : ∀ c' ≤ c, f c' = g c') :
    autStateCardFuelCharBody f c = autStateCardFuelCharBody g c := by
  rw [autStateCardFuelCharBody_eq, autStateCardFuelCharBody_eq]
  have h1 : c.unpair.2.unpair.1 ≤ c := le_trans (unpair_left_le c.unpair.2) (unpair_snd_le c)
  have h2 : c.unpair.2.unpair.2 ≤ c := le_trans (unpair_snd_le c.unpair.2) (unpair_snd_le c)
  rw [h _ h1, h _ h2]


theorem matchesBCharBody_eq (prev : ℕ → ℕ) (c cw : ℕ) :
    matchesBCharBody prev c cw =
      match c.unpair.1 with
      | 0 => 1
      | 1 => listEqChar cw c.unpair.2
      | 2 =>
        bExistsFn (matchesBCatG prev) (Nat.pair c cw) (listLenChar cw + 1)
      | 3 =>
        mulBit (prev (Nat.pair c.unpair.2.unpair.1 cw))
              (prev (Nat.pair c.unpair.2.unpair.2 cw))
      | _ => 0 := by
  unfold matchesBCharBody matchesBCatG
  match tag : c.unpair.1 with
  | 0 =>
    have h10 : (1 - 0 : ℕ) = 1 := rfl
    simp only [h10, isOne_one, selectFn_one]
  | 1 =>
    have h01 : (1 - 1 : ℕ) = 0 := rfl
    have h12 : (2 - 1 : ℕ) = 1 := rfl
    simp only [h01, h12, isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | 2 =>
    have h01 : (1 - 2 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12 : (2 - 2 : ℕ) = 0 := rfl
    have h23 : (3 - 2 : ℕ) = 1 := rfl
    simp only [h01, h23, isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | 3 =>
    have h01 : (1 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12 : (2 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h23 : (3 - 3 : ℕ) = 0 := rfl
    have h34 : (4 - 3 : ℕ) = 1 := rfl
    simp only [h01, h34, isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | t + 4 =>
    have hne1 : isOne (1 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    have hne2 : isOne (2 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    have hne3 : isOne (3 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    have hne4 : isOne (4 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    simp only [hne1, hne2, hne3, hne4, selectFn_zero]


private theorem c9b5_matchesBCatG_char (fuel : ℕ) (a b : SExpr) (w : List Bool) (i : ℕ) :
    matchesBCatG (fun p => matchesBChar fuel p.unpair.1 p.unpair.2)
        (Nat.pair i
          (Nat.pair (Nat.pair 2 (Nat.pair (c9b5_sexprGodelEncode a) (c9b5_sexprGodelEncode b)))
            (c9b5_encodeListBool w))) =
      mulBit (matchesBChar fuel (c9b5_sexprGodelEncode a) (takeCode i (c9b5_encodeListBool w)))
        (matchesBChar fuel (c9b5_sexprGodelEncode b) (dropCode i (c9b5_encodeListBool w))) := by
  simp [matchesBCatG]

set_option maxHeartbeats 1600000 in
theorem matchesBChar_eq_one_iff {fuel : ℕ} {e : SExpr} {w : List Bool}
    (h : c9b5_sexprDepth e ≤ fuel) :
    matchesBChar fuel (c9b5_sexprGodelEncode e) (c9b5_encodeListBool w) = 1 ↔
      matchesB e w = true := by
  induction e generalizing fuel w with
  | sigma =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel => simp [matchesBChar, matchesBCharBody_eq, matchesB, c9b5_sexprGodelEncode]
  | single σ =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel =>
      simp [matchesBChar, matchesBCharBody_eq, c9b5_sexprGodelEncode, matchesB,
        c9b5_listEqChar_encodeListBool w σ, decide_eq_true_eq]
  | cat a b iha ihb =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel =>
      have ha : c9b5_sexprDepth a ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      have hb : c9b5_sexprDepth b ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      have hbody := matchesBCharBody_eq (fun p => matchesBChar fuel p.unpair.1 p.unpair.2)
          (c9b5_sexprGodelEncode (.cat a b)) (c9b5_encodeListBool w)
      rw [matchesBChar, hbody]
      simp only [c9b5_sexprGodelEncode, unpair_pair_fst, matchesB, List.any_eq_true]
      rw [bExistsFn_eq_one_iff]
      have hlen : listLenChar (c9b5_encodeListBool w) + 1 = w.length + 1 := by
        simp [listLenChar_eq, c9b5_decodeList_encodeListBool, List.length_map]
      constructor
      · intro ⟨i, hi, hg⟩
        rw [c9b5_matchesBCatG_char, mulBit_eq_one_iff] at hg
        obtain ⟨h1, h2⟩ := hg
        have hi' : i < w.length + 1 := by rw [← hlen]; exact hi
        refine ⟨i, (List.mem_range).2 hi', ?_⟩
        simp only [Bool.and_eq_true]
        exact ⟨(iha ha).mp (by rw [← c9b5_takeCode_encodeListBool w i]; exact h1),
          (ihb hb).mp (by rw [← c9b5_dropCode_encodeListBool w i]; exact h2)⟩
      · intro ⟨i, hi, hfg⟩
        have hi' : i < listLenChar (c9b5_encodeListBool w) + 1 := by
          rw [hlen]; exact (List.mem_range).1 hi
        refine ⟨i, hi', ?_⟩
        rw [c9b5_matchesBCatG_char, mulBit_eq_one_iff]
        simp [Bool.and_eq_true] at hfg
        refine And.intro ?h1 ?h2
        · simpa [c9b5_takeCode_encodeListBool w i] using (iha ha).mpr hfg.1
        · simpa [c9b5_dropCode_encodeListBool w i] using (ihb hb).mpr hfg.2
  | cap a b iha ihb =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel =>
      have ha : c9b5_sexprDepth a ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      have hb : c9b5_sexprDepth b ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      have hbody := matchesBCharBody_eq (fun p => matchesBChar fuel p.unpair.1 p.unpair.2)
          (c9b5_sexprGodelEncode (.cap a b)) (c9b5_encodeListBool w)
      rw [matchesBChar, hbody]
      simp only [c9b5_sexprGodelEncode, unpair_pair_fst, unpair_pair_snd, matchesB, mulBit_eq_one_iff]
      constructor
      · intro ⟨h1, h2⟩
        rw [Bool.and_eq_true]
        exact ⟨(iha ha).mp h1, (ihb hb).mp h2⟩
      · intro hfg
        rw [Bool.and_eq_true] at hfg
        exact ⟨(iha ha).mpr hfg.1, (ihb hb).mpr hfg.2⟩

set_option maxHeartbeats 800000 in
private theorem primrec_matchesBCatG {prev : ℕ → ℕ} (hprev : Nat.Primrec prev) :
    Nat.Primrec (fun p => matchesBCatG prev p) := by
  have hc := Nat.Primrec.left.comp Nat.Primrec.right
  have ha := Nat.Primrec.left.comp (Nat.Primrec.right.comp hc)
  have hb := Nat.Primrec.right.comp (Nat.Primrec.right.comp hc)
  have hcw := Nat.Primrec.right.comp Nat.Primrec.right
  have hi := Nat.Primrec.left
  have h1 := hprev.comp (Nat.Primrec.pair ha (primrec_takeCode.comp (hi.pair hcw)))
  have h2 := hprev.comp (Nat.Primrec.pair hb (primrec_dropCode.comp (hi.pair hcw)))
  exact (primrec_mul₂ h1 h2).of_eq fun p => by
    dsimp [matchesBCatG, mulBit]
    simp only [unpair_pair_fst, unpair_pair_snd]

set_option maxHeartbeats 800000 in
theorem primrec_matchesBCharBody {prev : ℕ → ℕ} (hprev : Nat.Primrec prev) :
    Nat.Primrec (fun t => matchesBCharBody prev t.unpair.1 t.unpair.2) := by
  have htag : Nat.Primrec (fun t => (t.unpair.1).unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have h01 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) htag)
  have h12 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 2) htag)
  have h23 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 3) htag)
  have h34 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 4) htag)
  have hf1 := primrec_listEqChar.comp (Nat.Primrec.pair Nat.Primrec.right
    (Nat.Primrec.right.comp Nat.Primrec.left))
  have hpack : Nat.Primrec (fun t => Nat.pair t (listLenChar t.unpair.2 + 1)) :=
    Nat.Primrec.pair primrec_id
      (primrec_add₂ (primrec_listLenChar.comp Nat.Primrec.right) (Nat.Primrec.const 1))
  have hcat := (primrec_bExistsFn (primrec_matchesBCatG hprev)).comp hpack
  have hc := Nat.Primrec.left
  have ha := Nat.Primrec.left.comp (Nat.Primrec.right.comp hc)
  have hb := Nat.Primrec.right.comp (Nat.Primrec.right.comp hc)
  have hcw := Nat.Primrec.right
  have hcap := primrec_mulBit.comp (Nat.Primrec.pair
    (hprev.comp (Nat.Primrec.pair ha hcw)) (hprev.comp (Nat.Primrec.pair hb hcw)))
  exact (primrec_selectFn h01 (Nat.Primrec.const 1)
    (primrec_selectFn h12 hf1
      (primrec_selectFn h23 hcat
        (primrec_selectFn h34 hcap (Nat.Primrec.const 0))))).of_eq fun t => by
    rw [matchesBCharBody_eq]
    match tag : (t.unpair.1).unpair.1 with
    | 0 | 1 | 2 | 3 =>
      simp [selectFn, isOne, mulBit]
    | _ + 4 =>
      simp [selectFn, isOne, mulBit]

theorem matchesBChar_le_one : ∀ fuel c cw, matchesBChar fuel c cw ≤ 1
  | 0, _, _ => by simp [matchesBChar]
  | fuel + 1, c, cw => by
    rw [matchesBChar, matchesBCharBody_eq]
    match tag : c.unpair.1 with
    | 0 => simp
    | 1 => exact listEqChar_le_one _ _
    | 2 => exact bExistsFn_le_one _ _ _
    | 3 =>
      exact mulBit_le_one (matchesBChar_le_one fuel _ _) (matchesBChar_le_one fuel _ _)
    | _ + 4 => simp

/-! ### `matchesBChar` jointly primitive recursive in `(fuel, code)`, `code := pair c cw`

Harder than `decodeFuelOkChar`/`autStateCardFuelChar`: the cat branch's recursive calls are at
`pair a.unpair.2.unpair.1 (takeCode i cw)` / `pair a.unpair.2.unpair.2 (dropCode i cw)` — the word
half is a *derived* code (`takeCode`/`dropCode`), not a plain `Nat.unpair` projection, so
`hlocal` additionally needs `takeCode_le`/`dropCode_le` (proved above) alongside `pair_le_pair`. -/

theorem matchesBCharBody_local (f g : ℕ → ℕ) (c cw : ℕ)
    (h : ∀ p ≤ Nat.pair c cw, f p = g p) : matchesBCharBody f c cw = matchesBCharBody g c cw := by
  rw [matchesBCharBody_eq, matchesBCharBody_eq]
  match tag : c.unpair.1 with
  | 0 => rfl
  | 1 => rfl
  | 2 =>
    simp
    apply bExistsFn_congr
    intro i _
    unfold matchesBCatG
    simp only [unpair_pair_fst, unpair_pair_snd]
    have h1 : Nat.pair c.unpair.2.unpair.1 (takeCode i cw) ≤ Nat.pair c cw :=
      pair_le_pair (le_trans (unpair_left_le c.unpair.2) (unpair_snd_le c)) (takeCode_le i cw)
    have h2 : Nat.pair c.unpair.2.unpair.2 (dropCode i cw) ≤ Nat.pair c cw :=
      pair_le_pair (le_trans (unpair_snd_le c.unpair.2) (unpair_snd_le c)) (dropCode_le i cw)
    rw [h _ h1, h _ h2]
  | 3 =>
    simp
    have h1 : Nat.pair c.unpair.2.unpair.1 cw ≤ Nat.pair c cw :=
      pair_le_pair (le_trans (unpair_left_le c.unpair.2) (unpair_snd_le c)) (le_refl cw)
    have h2 : Nat.pair c.unpair.2.unpair.2 cw ≤ Nat.pair c cw :=
      pair_le_pair (le_trans (unpair_snd_le c.unpair.2) (unpair_snd_le c)) (le_refl cw)
    rw [h _ h1, h _ h2]
  | _ + 4 => rfl


/-! ## Exercise 7.22 C9b6 — `decideNonemptyBChar`, `consistentBChar`

Bounded index search over valid bit-list codes (via `codeBound`) instead of materializing
`wordsUpToCode`. -/


/-- `Nat.pair 0 t < Nat.pair 1 b` whenever `t < b`, via mathlib's `Nat.pair` monotonicity
in each argument (`pair_lt_pair_right` then `pair_lt_pair_left`). -/
private theorem pair_lt_pair_zero_right {t b : ℕ} (ht : t < b) :
    Nat.pair 0 t < Nat.pair 1 b :=
  lt_trans (Nat.pair_lt_pair_right 0 ht) (Nat.pair_lt_pair_left b Nat.zero_lt_one)

theorem codeBound_ge (n c : ℕ) (hlen : (decodeList c).length ≤ n)
    (hbin : ∀ x ∈ decodeList c, x ≤ 1) : c < codeBound n := by
  induction n generalizing c with
  | zero =>
    have hc : c = 0 := by
      cases c with
      | zero => rfl
      | succ c' => simp [decodeList_succ, List.length_cons] at hlen
    simp [hc, codeBound]
  | succ n ih =>
    cases c with
    | zero => simp [codeBound]
    | succ d =>
      simp only [decodeList_succ, List.length_cons] at hlen
      simp only [decodeList_succ] at hbin
      have htlen : (decodeList d.unpair.2).length ≤ n := by omega
      have htbin : ∀ x ∈ decodeList d.unpair.2, x ≤ 1 := fun x hx =>
        hbin x (List.mem_cons.mpr (Or.inr hx))
      have ht := ih d.unpair.2 htlen htbin
      have hh : d.unpair.1 ≤ 1 := hbin d.unpair.1 (List.mem_cons.mpr (Or.inl rfl))
      have hpair : Nat.pair d.unpair.1 d.unpair.2 < Nat.pair 1 (codeBound n) := by
        rcases (show d.unpair.1 = 0 ∨ d.unpair.1 = 1 by omega) with h0 | h1
        · rw [h0]; exact pair_lt_pair_zero_right ht
        · rw [h1]; exact Nat.pair_lt_pair_right 1 ht
      rw [Nat.pair_unpair] at hpair
      simp only [codeBound]
      omega

private theorem c9b6_allBinDigitsChar_encodeListBool (w : List Bool) :
    allBinDigitsChar (c9b5_encodeListBool w) = 1 := by
  rw [allBinDigitsChar_eq_one_iff]
  intro x hx
  rw [c9b5_decodeList_encodeListBool] at hx
  simp only [List.mem_map] at hx
  obtain ⟨b, _, hb⟩ := hx
  cases b <;> simp [c9b5_boolNat] at hb <;> omega

private theorem c9b6_encodeListBool_lt_codeBound {n : ℕ} {w : List Bool} (hw : w.length ≤ n) :
    c9b5_encodeListBool w < codeBound n := by
  apply codeBound_ge n (c9b5_encodeListBool w)
  · rw [c9b5_decodeList_encodeListBool, List.length_map]; exact hw
  · intro x hx
    rw [c9b5_decodeList_encodeListBool] at hx
    simp only [List.mem_map] at hx
    obtain ⟨b, _, hb⟩ := hx
    cases b <;> simp [c9b5_boolNat] at hb <;> omega


private theorem c9b6_boolNat_decide_eq (x : ℕ) (hx : x = 0 ∨ x = 1) :
    c9b5_boolNat (decide (x = 1)) = x := by
  rcases hx with rfl | rfl <;> simp [c9b5_boolNat]

/-- Round-trip through `c9b5_encodeListBool`/`c9b6_decodeListBool` for a code known to consist
only of binary digits (i.e. `allBinDigitsChar c = 1`). -/
private theorem c9b6_encodeListBool_decodeListBool_of_allBin {c : ℕ}
    (hall : allBinDigitsChar c = 1) :
    c9b5_encodeListBool (c9b6_decodeListBool c) = c := by
  rw [allBinDigitsChar_eq_one_iff] at hall
  apply c9b5_decodeList_injective
  rw [c9b5_decodeList_encodeListBool, c9b6_decodeListBool, List.map_map]
  conv_rhs => rw [← List.map_id (decodeList c)]
  exact List.map_congr_left (fun x hx => c9b6_boolNat_decide_eq x (hall x hx))

private theorem c9b6_matchesBChar_of_allBin {fuel : ℕ} {e : SExpr} {c : ℕ}
    (h : c9b5_sexprDepth e ≤ fuel) (hall : allBinDigitsChar c = 1)
    (hmatch : matchesBChar fuel (c9b5_sexprGodelEncode e) c = 1) :
    matchesB e (c9b6_decodeListBool c) = true := by
  apply (matchesBChar_eq_one_iff (w := c9b6_decodeListBool c) h).1
  rwa [c9b6_encodeListBool_decodeListBool_of_allBin hall]


theorem decideNonemptyBChar_eq_one_iff {fuel : ℕ} {e : SExpr}
    (h : c9b5_sexprDepth e ≤ fuel) :
    decideNonemptyBChar fuel (c9b5_sexprGodelEncode e) = 1 ↔ (denote e).Nonempty := by
  simp only [decideNonemptyBChar, bExistsFn_eq_one_iff, unpair_pair_fst, unpair_pair_snd,
    mulBit_eq_one_iff]
  constructor
  · rintro ⟨i, -, hall, hmatch⟩
    exact ⟨c9b6_decodeListBool i, (matchesB_iff e _).mp (c9b6_matchesBChar_of_allBin h hall hmatch)⟩
  · intro hne
    obtain ⟨w, hwmem, hmatch⟩ := (denote_nonempty_iff_short e).mp hne
    refine ⟨c9b5_encodeListBool w, ?_, c9b6_allBinDigitsChar_encodeListBool w,
      (matchesBChar_eq_one_iff h).2 hmatch⟩
    rw [autStateCardFuelChar_eq_autStateCard h]
    exact c9b6_encodeListBool_lt_codeBound (by rwa [mem_wordsUpTo] at hwmem)


theorem c9b6_sexprGodelEncode_cap (a b : SExpr) :
    c9b5_sexprGodelEncode (.cap a b) = capCode (c9b5_sexprGodelEncode a) (c9b5_sexprGodelEncode b) :=
  rfl


/-! ### `decideNonemptyBChar`/`consistentBChar` jointly primitive recursive in `(fuel, code)`

Both are built from `matchesBChar`/`autStateCardFuelChar` via `bExistsFn`/`codeBound`, so once
those two are jointly primitive recursive (above), only the parametrized `bExistsFn` bridge
(`primrec_bExistsFn_param`, threading `fuel` through the search) is needed — no new
course-of-values machinery. -/

/-! ## Exercise 7.22k (Session C7b, optional) — `subsetBChar`, `interEqChar`

`Exercise722Equiv.lean` builds a *Bool-level* decider `interEqB` for language equivalence
(`denote e₁ = denote e₂`), via a choice-free `Finset`-valued subset-construction simulation of
`toNFA e` (needed since `.cat` makes `toNFA e` genuinely nondeterministic — "e₂ rejects w" is a
universal statement over nondeterministic paths, which doesn't pump the way existential
acceptance does). That construction is cited here **only** for its length bound
(`exists_diff_word_short`, wrapped in `subsetB_iff`/`interEqB_iff`); the numeric mirror below does
**not** re-encode `Finset (autState e)` at all — `interEqB`'s own definition is just a bounded
search calling `matchesB`, which already has a joint `(fuel, code)`-primitive-recursive mirror
(`matchesBChar`, C9b5/C9b8). Only the *bound formula* and the *bounded-forall* wiring are new. -/


theorem subsetGuardChar_le_one (fuel c1 c2 i : ℕ) : subsetGuardChar fuel c1 c2 i ≤ 1 :=
  mulBit_le_one (allBinDigitsChar_le_one _) (isOne_le_one _)


set_option maxHeartbeats 800000 in
theorem subsetBChar_eq_one_iff {fuel : ℕ} {e1 e2 : SExpr}
    (h1 : c9b5_sexprDepth e1 ≤ fuel) (h2 : c9b5_sexprDepth e2 ≤ fuel) :
    subsetBChar fuel (c9b5_sexprGodelEncode e1) (c9b5_sexprGodelEncode e2) = 1 ↔
      denote e1 ⊆ denote e2 := by
  rw [← subsetB_iff]
  have hbound : subsetBoundChar fuel (c9b5_sexprGodelEncode e1) (c9b5_sexprGodelEncode e2) =
      Fintype.card (Finset (autState e1) × Finset (autState e2)) := by
    unfold subsetBoundChar
    rw [autStateCardFuelChar_eq_autStateCard h1, autStateCardFuelChar_eq_autStateCard h2,
      autStateCard_eq_card, autStateCard_eq_card, Fintype.card_prod, Fintype.card_finset,
      Fintype.card_finset]
  unfold subsetB subsetBChar
  rw [List.all_eq_true, bForallFn_eq_one_iff]
  simp only [unpair_pair_fst, unpair_pair_snd, hbound]
  constructor
  · intro h w hwmem
    rw [mem_wordsUpTo] at hwmem
    have hi := h (c9b5_encodeListBool w) (c9b6_encodeListBool_lt_codeBound hwmem)
    have hguard1 : subsetGuardChar fuel (c9b5_sexprGodelEncode e1) (c9b5_sexprGodelEncode e2)
        (c9b5_encodeListBool w) = 1 := by
      unfold subsetGuardChar
      rw [c9b6_allBinDigitsChar_encodeListBool, mulBit, one_mul, listLenChar_eq,
        c9b5_decodeList_encodeListBool, List.length_map, hbound,
        Nat.sub_eq_zero_of_le hwmem]
      exact isOne_one
    rw [hguard1, selectFn_one] at hi
    by_cases hc1 : matchesBChar fuel (c9b5_sexprGodelEncode e1) (c9b5_encodeListBool w) = 1
    · rw [hc1, selectFn_one] at hi
      simp only [Bool.or_eq_true]
      exact Or.inr ((matchesBChar_eq_one_iff h2).mp hi)
    · have hc1' : matchesBChar fuel (c9b5_sexprGodelEncode e1) (c9b5_encodeListBool w) = 0 := by
        have := matchesBChar_le_one fuel (c9b5_sexprGodelEncode e1) (c9b5_encodeListBool w)
        omega
      simp only [Bool.or_eq_true]
      refine Or.inl ?_
      by_contra hcontra
      exact hc1 ((matchesBChar_eq_one_iff h1).mpr (by simpa using hcontra))
  · intro h i _
    rcases (show subsetGuardChar fuel (c9b5_sexprGodelEncode e1) (c9b5_sexprGodelEncode e2) i = 0 ∨
        subsetGuardChar fuel (c9b5_sexprGodelEncode e1) (c9b5_sexprGodelEncode e2) i = 1 from by
      have := subsetGuardChar_le_one fuel (c9b5_sexprGodelEncode e1) (c9b5_sexprGodelEncode e2) i
      omega) with hguard | hguard
    · rw [hguard, selectFn_zero]
    · rw [hguard, selectFn_one]
      unfold subsetGuardChar at hguard
      rw [mulBit_eq_one_iff, isOne_eq_one_iff] at hguard
      obtain ⟨hallbin, hlen0⟩ := hguard
      have hlenle : listLenChar i ≤
          Fintype.card (Finset (autState e1) × Finset (autState e2)) := by omega
      have hieq : c9b5_encodeListBool (c9b6_decodeListBool i) = i :=
        c9b6_encodeListBool_decodeListBool_of_allBin hallbin
      have hwlen : (c9b6_decodeListBool i).length ≤
          Fintype.card (Finset (autState e1) × Finset (autState e2)) := by
        unfold c9b6_decodeListBool
        rw [List.length_map]
        rwa [listLenChar_eq] at hlenle
      have hwmem := (mem_wordsUpTo _).mpr hwlen
      have hspec := h (c9b6_decodeListBool i) hwmem
      rw [← hieq]
      by_cases hc1 : matchesBChar fuel (c9b5_sexprGodelEncode e1) (c9b5_encodeListBool
          (c9b6_decodeListBool i)) = 1
      · rw [hc1, selectFn_one]
        have hc1matches : matchesB e1 (c9b6_decodeListBool i) = true :=
          (matchesBChar_eq_one_iff h1).mp hc1
        simp only [Bool.or_eq_true] at hspec
        rcases hspec with hf | ht
        · rw [hc1matches] at hf; simp at hf
        · exact (matchesBChar_eq_one_iff h2).mpr ht
      · have hc1' : matchesBChar fuel (c9b5_sexprGodelEncode e1)
            (c9b5_encodeListBool (c9b6_decodeListBool i)) = 0 := by
          have := matchesBChar_le_one fuel (c9b5_sexprGodelEncode e1)
            (c9b5_encodeListBool (c9b6_decodeListBool i))
          omega
        rw [hc1', selectFn_zero]

end Domain.Recursive
