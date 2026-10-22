module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.LFunData
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.BasicInst2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.bitToNat_false
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.bitToNat_true
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.embStr_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_two

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)

variable {β γ δ : Type*}

/-- **The one use of `Classical.choice` in this section.** Every `ComputablePresentation P` of a
`V` yields *some* `LFunData P`, by choosing concrete deciders out of `Lpres`'s and `P`'s existential
`incl_computable`/`cons_computable`/`eq_computable` witnesses. -/
noncomputable def LFunData.ofPresentation {V : NeighborhoodSystem β} (P : ComputablePresentation V) :
    LFunData P where
  gN := funConsChar Lpres P Lpres.cons_computable.choose P.cons_computable.choose
  incl0 := Lpres.incl_computable.choose
  incl1 := P.incl_computable.choose
  eq1 := P.eq_computable.choose
  hgN := funConsChar_spec Lpres P Lpres.cons_computable.choose P.cons_computable.choose
    (fun s => (Lpres.cons_computable.choose_spec.2 s).symm)
    (fun s => (P.cons_computable.choose_spec.2 s).symm)
  hgNp := primrec_funConsChar Lpres P Lpres.cons_computable.choose P.cons_computable.choose
    Lpres.cons_computable.choose_spec.1 P.cons_computable.choose_spec.1
  hincl0 := fun s => (Lpres.incl_computable.choose_spec.2 s).symm
  hincl0p := Lpres.incl_computable.choose_spec.1
  hincl1 := fun s => (P.incl_computable.choose_spec.2 s).symm
  hincl1p := P.incl_computable.choose_spec.1
  heq1 := fun s => (P.eq_computable.choose_spec.2 s).symm
  heq1p := P.eq_computable.choose_spec.1

end DomainTheory.NeighbourhoodSystems.Exercise724
