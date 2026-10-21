/-ai
An element of the function-space presentation is a computable element if and only if the approximable map it determines is a computable map of the two component presentations. This is Theorem 7.5 packaged for funPresentation.

The equivalence is the corresponding characterization for the enumerated neighbourhoods of the presentation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum_isComputableElement_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)








































































































/-- **Theorem 7.5 (Scott 1981, PRG-19), packaged for `funPresentation`.** An element of the
function-space presentation is a computable element iff it is (the filter of) a computable map. -/
theorem isComputableElement_funPresentation_iff (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₁.X s.unpair.1 = P₁.X s.unpair.2) (heq1p : Nat.Primrec eq1)
    (φ : (funSpace V₀ V₁).Element) :
    IsComputableElement (funPresentation P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
        hincl1 hincl1p heq1 heq1p) φ ↔ IsComputableMap P₀ P₁ (toApproxMap φ) :=
  Xenum_isComputableElement_iff P₀ P₁ gN hgNp hgN φ

end DomainTheory.NeighbourhoodSystems
