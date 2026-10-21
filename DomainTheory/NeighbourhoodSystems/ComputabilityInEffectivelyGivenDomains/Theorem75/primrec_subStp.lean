/-ai
If both inclusion characteristics are primitive recursive, then the step-function inclusion step is primitive recursive.

The flag, the parameter code, the input index, and the output index are primitive-recursive projections. The conditional output-intersection index of the parameter and the input index is primitive recursive by pairing those projections, and the codomain inclusion characteristic of that index against the output index is primitive recursive. Selection of the flag against that bit agrees with the step.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interYsIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.primrec_interYsIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.subStp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

theorem primrec_subStp (incl0 incl1 : ℕ → ℕ) (hincl0p : Nat.Primrec incl0)
    (hincl1p : Nat.Primrec incl1) : Nat.Primrec (subStp P₁ incl0 incl1) := by
  have hflag : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have ha : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have he2 : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hidx : Nat.Primrec
      (fun w : ℕ => interYsIdx P₁ incl0 w.unpair.2.unpair.2 w.unpair.1.unpair.1) :=
    ((primrec_interYsIdx P₁ incl0 hincl0p).comp (ha.pair hk)).of_eq (fun w => by
      show interYsIdx P₁ incl0 (Nat.pair w.unpair.2.unpair.2 w.unpair.1.unpair.1).unpair.1
        (Nat.pair w.unpair.2.unpair.2 w.unpair.1.unpair.1).unpair.2 = _
      rw [unpair_pair_fst, unpair_pair_snd])
  have hincl := hincl1p.comp (hidx.pair he2)
  refine (primrec_selectFn hflag (primrec_isOne.comp hincl) (Nat.Primrec.const 0)).of_eq (fun w => ?_)
  unfold subStp
  rfl

end DomainTheory.NeighbourhoodSystems
