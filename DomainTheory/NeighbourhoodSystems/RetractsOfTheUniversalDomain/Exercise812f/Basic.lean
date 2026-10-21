/-ai
This file gathers and re-exports the generic bisection split, the canonical bisection of U, the computable difference on V, the concrete split of V against U, and the proof that this split is computable.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812f.splitX812f
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812f.isComputableSplit_812f

@[expose] public section

/-!
# Exercise 8.12(f) (Scott 1981, PRG-19, Lecture VIII) — `V` satisfies the extension property
relative to `U`

The mirror image of `Exercise812eD.lean`'s `8.12(e)`: there `U` was the *prober* against `V`'s
canonical bisection (`SplitV.lean`'s `B812e`); here `V` is the *prober* against `U`'s canonical
bisection. Given `(e)(c)`'s generic `splitFromBisection`/`isComputableSplit_ofBisection`
(`Exercise812e.lean`), this is a one-line instantiation, fed:

* `VComputablePresentation` (`VComputablePresentation.lean`) as the prober `P`;
* `V_isComputableDiff` (`VDiff.lean`) as `P`'s `IsComputableDiff` witness — the missing
  prerequisite this development had to supply first (`U`'s side, `Udiff`/`U_isComputableDiff`, was
  already built for `(e)(d)`, but `V`'s side had never been instantiated);
* `UBisection2` (`UBisection2.lean`) as the target `U`'s `ComputableBisection` — **not**
  `SplitU.lean`'s `splitULeft`/`splitURight`, which split at the midpoint of `canonCode n`'s *first*
  presenting pair and so fail `ComputableBisection`'s `left_congr`/`right_congr` (two different
  canonical presenting lists of the same `U`-neighbourhood can have different first pairs). `UBisection2`
  instead splits at the midpoint of the presented set's own intrinsic `(min, max)` — genuine
  invariants of the set, not of its presentation — restoring well-definedness at no cost to any of
  `(e)(c)`'s other requirements.
* `V`'s already-`Pass` `IsPositive`/`NoMinimal`/`DiffClosed` facts (`Exercise812c.lean`), needed only
  for `isComputableSplit_ofBisection`'s correctness obligations (`(e)(c)`'s own congruence lemmas),
  exactly mirroring `(e)(d)`'s use of `U`'s analogous facts.
-/

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


end DomainTheory.NeighbourhoodSystems
