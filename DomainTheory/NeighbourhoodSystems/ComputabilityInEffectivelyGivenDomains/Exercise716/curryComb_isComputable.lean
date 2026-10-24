module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise716.curryStepCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise716.curryComb_rel_recDecidable

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}


/-- **Exercise 7.16 — `curry` is computable, and in fact a recursive set.** If `𝒟₀, 𝒟₁, 𝒟₂` are
effectively given, then there are computable presentations of `(𝒟₀×𝒟₁→𝒟₂)` and `(𝒟₀→(𝒟₁→𝒟₂))`
relative to which the `curry` combinator's neighbourhood relation is **recursively decidable**
(`RecDecidable₂`) — hence `curry` is a computable map (`ComputableMap`, the r.e. condition of
Definition 7.2). The answer to Scott's question: `curry` is a *recursive* set, not merely r.e. -/
theorem curryComb_isComputable
    (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
    (P₂ : ComputablePresentation V₂) :
    ∃ (PA : ComputablePresentation (funSpace (prod V₀ V₁) V₂))
      (PB : ComputablePresentation (funSpace V₀ (funSpace V₁ V₂))),
      RecDecidable₂ (fun n m => (curryC V₀ V₁ V₂).rel (PA.X n) (PB.X m)) ∧
        ComputableMap PA PB (curryC V₀ V₁ V₂) := by
  obtain ⟨incl0, hincl0p, hincl0s⟩ := P₀.incl_computable
  obtain ⟨fc0, hfc0p, hfc0s⟩ := P₀.cons_computable
  obtain ⟨incl1, hincl1p, hincl1s⟩ := P₁.incl_computable
  obtain ⟨fc1, hfc1p, hfc1s⟩ := P₁.cons_computable
  obtain ⟨incl2, hincl2p, hincl2s⟩ := P₂.incl_computable
  obtain ⟨eq2, heq2p, heq2s⟩ := P₂.eq_computable
  obtain ⟨fc2, hfc2p, hfc2s⟩ := P₂.cons_computable
  obtain ⟨inclpr, hinclprp, hinclprs⟩ := (prodPresentation P₀ P₁).incl_computable
  obtain ⟨fcpr, hfcprp, hfcprs⟩ := (prodPresentation P₀ P₁).cons_computable
  -- inner function space `Pc = (𝒟₁ → 𝒟₂)`
  let Pc : ComputablePresentation (funSpace V₁ V₂) :=
    funPresentation P₁ P₂ (funConsChar P₁ P₂ fc1 fc2) incl1 incl2 eq2
      (funConsChar_spec P₁ P₂ fc1 fc2 (fun s => (hfc1s s).symm) (fun s => (hfc2s s).symm))
      (primrec_funConsChar P₁ P₂ fc1 fc2 hfc1p hfc2p)
      (fun s => (hincl1s s).symm) hincl1p (fun s => (hincl2s s).symm) hincl2p
      (fun s => (heq2s s).symm) heq2p
  obtain ⟨inclc, hinclcp, hinclcs⟩ := Pc.incl_computable
  obtain ⟨eqc, heqcp, heqcs⟩ := Pc.eq_computable
  obtain ⟨fcc, hfccp, hfccs⟩ := Pc.cons_computable
  -- domain function space `PA = (𝒟₀×𝒟₁ → 𝒟₂)`
  let PA : ComputablePresentation (funSpace (prod V₀ V₁) V₂) :=
    funPresentation (prodPresentation P₀ P₁) P₂
      (funConsChar (prodPresentation P₀ P₁) P₂ fcpr fc2) inclpr incl2 eq2
      (funConsChar_spec (prodPresentation P₀ P₁) P₂ fcpr fc2
        (fun s => (hfcprs s).symm) (fun s => (hfc2s s).symm))
      (primrec_funConsChar (prodPresentation P₀ P₁) P₂ fcpr fc2 hfcprp hfc2p)
      (fun s => (hinclprs s).symm) hinclprp (fun s => (hincl2s s).symm) hincl2p
      (fun s => (heq2s s).symm) heq2p
  -- codomain function space `PB = (𝒟₀ → (𝒟₁ → 𝒟₂))`
  let PB : ComputablePresentation (funSpace V₀ (funSpace V₁ V₂)) :=
    funPresentation P₀ Pc (funConsChar P₀ Pc fc0 fcc) incl0 inclc eqc
      (funConsChar_spec P₀ Pc fc0 fcc (fun s => (hfc0s s).symm) (fun s => (hfccs s).symm))
      (primrec_funConsChar P₀ Pc fc0 fcc hfc0p hfccp)
      (fun s => (hincl0s s).symm) hincl0p (fun s => (hinclcs s).symm) hinclcp
      (fun s => (heqcs s).symm) heqcp
  have hRec : RecDecidable₂ (fun n m => (curryC V₀ V₁ V₂).rel (PA.X n) (PB.X m)) :=
    curryComb_rel_recDecidable P₀ P₁ P₂
      (funConsChar (prodPresentation P₀ P₁) P₂ fcpr fc2) (funConsChar P₀ Pc fc0 fcc)
      (funConsChar P₁ P₂ fc1 fc2) PA PB Pc rfl rfl rfl
      (funConsChar_spec (prodPresentation P₀ P₁) P₂ fcpr fc2
        (fun s => (hfcprs s).symm) (fun s => (hfc2s s).symm))
      (funConsChar_spec P₁ P₂ fc1 fc2 (fun s => (hfc1s s).symm) (fun s => (hfc2s s).symm))
      (primrec_funConsChar P₀ Pc fc0 fcc hfc0p hfccp)
      (primrec_funConsChar P₁ P₂ fc1 fc2 hfc1p hfc2p)
  exact ⟨PA, PB, hRec, ⟨hRec.re⟩⟩

end DomainTheory.NeighbourhoodSystems
