/-ai
Theorem 8.6 states that if E is effectively given, then sub, packaged as an endomap of the function space, is computable.

A computable presentation of E supplies primitive recursive characters for inclusion, equality, and consistency. Reindexing the inclusion and equality characters to pairs, and reading the consistency character through its specification, supplies the function-space presentation, and the computability of the packaged map applies to that presentation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86c.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86c.subApprox_isComputable

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6

variable {α : Type*} {E : NeighborhoodSystem α}



/-- **Theorem 8.6(c) (Scott 1981, PRG-19), in full: "If `E` is effectively given, then `sub` is
computable."** Packages `subApprox_isComputable` with the function-space presentation that Theorem
7.5 (`funSpace_isEffectivelyGiven`'s construction, `funPresentation`) builds out of any computable
presentation of `E`. -/
theorem sub_isComputable_of_isEffectivelyGiven (h : E.IsEffectivelyGiven) :
    ∃ Pfun : ComputablePresentation (funSpace E E),
      IsComputableMap Pfun Pfun (subApprox (E := E)) := by
  obtain ⟨P⟩ := h
  obtain ⟨incl, hinclp, hincls⟩ := P.incl_computable
  obtain ⟨eq, heqp, heqs⟩ := P.eq_computable
  obtain ⟨fc, hfcp, hfcs⟩ := P.cons_computable
  have hincl' : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2 := fun s => (hincls s).symm
  have heq' : ∀ s, eq s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2 := fun s => (heqs s).symm
  have hgN : ∀ c, funConsChar P P fc fc c = 1 ↔
      (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty :=
    fun c => funConsChar_spec P P fc fc (fun s => (hfcs s).symm) (fun s => (hfcs s).symm) c
  refine ⟨funPresentation P P (funConsChar P P fc fc) incl incl eq hgN
    (primrec_funConsChar P P fc fc hfcp hfcp) hincl' hinclp hincl' hinclp heq' heqp,
    subApprox_isComputable P (funConsChar P P fc fc) hgN incl eq
      (primrec_funConsChar P P fc fc hfcp hfcp) hincl' hinclp heq' heqp⟩

end DomainTheory.NeighbourhoodSystems
