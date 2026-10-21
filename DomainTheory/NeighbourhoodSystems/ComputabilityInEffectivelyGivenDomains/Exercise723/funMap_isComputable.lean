/-ai
The curried map funMap is computable relative to an arbitrary valid function-space presentation of PNpres with PNpres. The deciders gN, incl0, incl1, and eq1 are the nonempty, inclusion, and equality witnesses required by that presentation, each primitive recursive and correct on the stated equations.

The result is the generic currying theorem of Theorem 7.5, applied to the computability of gMap.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.gMap_isComputable

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.curry_isComputable
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


/-- **`fun` is computable**, relative to *any* valid function-space presentation
`funPresentation PNpres PNpres gN incl0 incl1 eq1 …` (Theorem 7.5's generic `curry_isComputable`,
fed `gMap_isComputable`). Every such presentation exists (`funSpace_isEffectivelyGiven`); this
result is stated generically over the witnessing deciders, exactly as `curry_isComputable` itself
is, rather than committing to one concrete choice of `gN`/`incl0`/`incl1`/`eq1` for `PN`. -/
theorem funMap_isComputable (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf PNpres PNpres (decodeList c))
      : Set (ApproximableMap PN PN)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ PNpres.X s.unpair.1 ⊆ PNpres.X s.unpair.2)
    (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ PNpres.X s.unpair.1 ⊆ PNpres.X s.unpair.2)
    (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ PNpres.X s.unpair.1 = PNpres.X s.unpair.2) (heq1p : Nat.Primrec eq1) :
    IsComputableMap PNpres
      (funPresentation PNpres PNpres gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p hincl1 hincl1p
        heq1 heq1p)
      funMap :=
  curry_isComputable PNpres PNpres PNpres gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p hincl1
    hincl1p heq1 heq1p gMap_isComputable

end DomainTheory.NeighbourhoodSystems.Exercise723
