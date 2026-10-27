# Exercise 8.12

**EXERCISE 8.12.** Generalize the notation $2X + 1$ for subsets $X \subseteq \mathbb{N}$ to sets of the form

$$2^k X + \ell, \quad \text{where } \ell < 2^k.$$

Let $V$ be the non-empty finite unions of sets $2^k \mathbb{N} + \ell$. Show that $U \cong V$ and that the isomorphism is effective, thus obtaining another presentation of $U$.

## Tip summary

Scott’s claim is a single conjunction: $V$ is effectively given, and $U$ is effectively isomorphic to $V$. The Lean tip `exercise_8_12` packages exactly that, assembling `V_isEffectivelyGiven` with the concrete effective isomorphism `effectiveIso812_UV`.


## Development

Scott gives no written proof—only the construction of $V$ and the demand that the isomorphism be effective. The formalization therefore supplies a structured development under the exercise: present $V$, build an abstract domain isomorphism, make it effective, equip both sides with computable bisections/splits, and assemble the effective iso.

### Presenting $V$

The integer neighbourhood system $V$ is built from affine residue classes $2^k\mathbb{N}+\ell$ and their non-empty finite unions. Its computable presentation (indices, decoding, intersection/union/difference codes, and the canonical bisection `splitV*`) lives in a dedicated library module so earlier Scott numbers can use it without importing Exercise 8.14’s tip.

**[VComputablePresentation.lean](VComputablePresentation.lean)** — computable presentation of $V$, including `VComputablePresentation` and `V_isEffectivelyGiven`

@import "VComputablePresentation.lean"

### Abstract isomorphism (8.12(c))

Given two positive, difference-closed, atomless neighbourhood systems with enumerations that cover every neighbourhood and start at the master set, one builds paired atom sequences (`XPseq`/`YPseq`) from mutual `SplitSpec'` probes and obtains a domain isomorphism. The headline is `isomorphic_812c`.

**[domainIso812c.lean](domainIso812c.lean)** — difference-closure / no-minimal apparatus, atom pairing, and `isomorphic_812c`

@import "domainIso812c.lean"

### Effective isomorphism (8.12(d))

The same back-and-forth is carried out on computable presentations: coded atom sequences, primitivity of the step maps, and the order isomorphism `domainIsoCode812d` lift to an `EffectiveIso`. The generic assembly is `effectiveIso812d`.

**[effectiveIso812d.lean](effectiveIso812d.lean)** — coded pairing, primrec witnesses, and `effectiveIso812d`

@import "effectiveIso812d.lean"

### Computable split of $U$ against $V$ (8.12(e))

With `U`’s computable difference and $V$’s bisection in hand, `splitX812e` is the concrete `IsComputableSplit` of $U$ probing $V$ (`isComputableSplit.«812e»`).

**[splitX812e.lean](splitX812e.lean)** — `U_isComputableDiff`, `splitX812e`, and `isComputableSplit.«812e»`

@import "splitX812e.lean"

### Symmetric split and UV assembly (8.12(f)–(g))

The mirror split `splitX812f` ( $V$ probing $U$ via `UBisection2`), both `SplitSpec'` halves, computable unions, and the final `EffectiveIso U V` are assembled as `effectiveIso812_UV`.

**[effectiveIso812_UV.lean](effectiveIso812_UV.lean)** — `«812f»`, `hxSplit812e`/`hySplit812f`, unions, and `effectiveIso812_UV`

@import "effectiveIso812_UV.lean"

The tip then simply pairs effective givenness of $V$ with that isomorphism, which is Exercise 8.12 in Scott’s sense.

**[Exercise_8_12.lean](Exercise_8_12.lean)** — Scott tip `exercise_8_12`

@import "Exercise_8_12.lean"
