/-ai
If an approximable map is computable, then its power-domain action is a computable map between the canonical power-domain presentations built from primitive-recursive consistency deciders.

This is the recursive enumerability of the relation on power-domain codes.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PFmap_isComputable_Ypd

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}


/-- **Exercise 7.19 (Scott's first question), packaged.** `ℙf` is a computable map between the
canonical effective presentations `ℙ𝒟`, `ℙℰ` (Proposition 7.10) whenever `f` is computable. -/
theorem PFmap_isComputable (P : ComputablePresentation V) (Q : ComputablePresentation W)
    (consV : ℕ → ℕ) (hconsVp : Nat.Primrec consV)
    (hconsVs : ∀ a b, consV (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b)
    (consW : ℕ → ℕ) (hconsWp : Nat.Primrec consW)
    (hconsWs : ∀ a b, consW (Nat.pair a b) = 1 ↔ ∃ k, Q.X k ⊆ Q.X a ∩ Q.X b)
    {f : ApproximableMap V W} (hf : IsComputableMap P Q f) :
    IsComputableMap (V.PDPresentation P consV hconsVp hconsVs)
      (W.PDPresentation Q consW hconsWp hconsWs) (PFmap f) := by
  exact PFmap_isComputable_Ypd P Q hf

end DomainTheory.NeighbourhoodSystems
