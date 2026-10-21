/-ai
The sharp decider step is primitive recursive whenever the consistency, equality, and intersection functions of D are primitive recursive.

The index projections, the halved indices, and the two memo lookups are primitive recursive by composition, division by two, subtraction, and binary list lookup. Packing three primitive-recursive functions is primitive recursive. The leaf pack, the zero pack, and the node pack, whose bits are products of equality and consistency bits and whose index is built from the intersection indices, are therefore primitive recursive. Nesting the selections of the step and rewriting along the definition gives the claim.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.primrec_listGet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.primrec_listGet₂
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

/-- The decider step is primitive recursive when the `D`-level functions are. -/
theorem primrec_dsharpStep (hfcons : Nat.Primrec fcons) (hfeq : Nat.Primrec feq)
    (hfinter : Nat.Primrec finter) : Nat.Primrec (dsharpStep fcons feq finter) := by
  have hi : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hj : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have htbl : Nat.Primrec (fun p : ℕ => p.unpair.2) := Nat.Primrec.right
  have hw : Nat.Primrec (fun p : ℕ => p.unpair.1) := Nat.Primrec.left
  have hidiv : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.1 / 2) := primrec_div2.comp hi
  have hjdiv : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2 / 2) := primrec_div2.comp hj
  have hna : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.1 / 2 - 1) :=
    primrec_sub₂ hidiv (Nat.Primrec.const 1)
  have hnb : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2 / 2 - 1) :=
    primrec_sub₂ hjdiv (Nat.Primrec.const 1)
  have hv1 : Nat.Primrec (fun p : ℕ =>
      Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1 (p.unpair.1.unpair.2 / 2 - 1).unpair.1) :=
    (Nat.Primrec.left.comp hna).pair (Nat.Primrec.left.comp hnb)
  have hv2 : Nat.Primrec (fun p : ℕ =>
      Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2 (p.unpair.1.unpair.2 / 2 - 1).unpair.2) :=
    (Nat.Primrec.right.comp hna).pair (Nat.Primrec.right.comp hnb)
  have hr1 : Nat.Primrec (fun p : ℕ => listGet p.unpair.2
      (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
        (p.unpair.1.unpair.2 / 2 - 1).unpair.1)) :=
    primrec_listGet₂ htbl (primrec_sub₂ (primrec_sub₂ hw (Nat.Primrec.const 1)) hv1)
  have hr2 : Nat.Primrec (fun p : ℕ => listGet p.unpair.2
      (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
        (p.unpair.1.unpair.2 / 2 - 1).unpair.2)) :=
    primrec_listGet₂ htbl (primrec_sub₂ (primrec_sub₂ hw (Nat.Primrec.const 1)) hv2)
  have hidiv2 : Nat.Primrec (fun p : ℕ => Nat.pair (p.unpair.1.unpair.1 / 2) (p.unpair.1.unpair.2 / 2)) :=
    hidiv.pair hjdiv
  have hpackT : ∀ {e c ii : ℕ → ℕ}, Nat.Primrec e → Nat.Primrec c → Nat.Primrec ii →
      Nat.Primrec (fun p => packT (e p) (c p) (ii p)) := by
    intro e c ii he hc hii
    exact (he.pair (hc.pair hii)).of_eq fun p => rfl
  have hleaf : Nat.Primrec (fun p : ℕ =>
      packT (feq (Nat.pair (p.unpair.1.unpair.1 / 2) (p.unpair.1.unpair.2 / 2)))
        (fcons (Nat.pair (p.unpair.1.unpair.1 / 2) (p.unpair.1.unpair.2 / 2)))
        (2 * finter (Nat.pair (p.unpair.1.unpair.1 / 2) (p.unpair.1.unpair.2 / 2)) + 1)) :=
    hpackT (hfeq.comp hidiv2) (hfcons.comp hidiv2)
      (Nat.Primrec.succ.comp (primrec_mul₂ (Nat.Primrec.const 2) (hfinter.comp hidiv2)))
  have hzero : Nat.Primrec (fun _ : ℕ => packT 0 0 0) := Nat.Primrec.const _
  have heqB1 : Nat.Primrec (fun p => eqB _) := Nat.Primrec.left.comp hr1
  have heqB2 : Nat.Primrec (fun p => eqB _) := Nat.Primrec.left.comp hr2
  have hconsB1 : Nat.Primrec (fun p => consB _) := (Nat.Primrec.left.comp Nat.Primrec.right).comp hr1
  have hconsB2 : Nat.Primrec (fun p => consB _) := (Nat.Primrec.left.comp Nat.Primrec.right).comp hr2
  have hintI1 : Nat.Primrec (fun p => intI _) := (Nat.Primrec.right.comp Nat.Primrec.right).comp hr1
  have hintI2 : Nat.Primrec (fun p => intI _) := (Nat.Primrec.right.comp Nat.Primrec.right).comp hr2
  have hnode : Nat.Primrec (fun p : ℕ =>
      packT (eqB (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
                (p.unpair.1.unpair.2 / 2 - 1).unpair.1))
            * eqB (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
                (p.unpair.1.unpair.2 / 2 - 1).unpair.2)))
        (consB (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
                (p.unpair.1.unpair.2 / 2 - 1).unpair.1))
            * consB (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
                (p.unpair.1.unpair.2 / 2 - 1).unpair.2)))
        (2 * Nat.pair (intI (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
                (p.unpair.1.unpair.2 / 2 - 1).unpair.1)))
              (intI (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
                (p.unpair.1.unpair.2 / 2 - 1).unpair.2))) + 2)) :=
    hpackT (primrec_mul₂ heqB1 heqB2) (primrec_mul₂ hconsB1 hconsB2)
      ((Nat.Primrec.succ.comp Nat.Primrec.succ).comp (primrec_mul₂ (Nat.Primrec.const 2)
        (hintI1.pair hintI2)))
  refine (primrec_selectFn (primrec_sub₂ (Nat.Primrec.const 1) hi)
    (hpackT (primrec_sub₂ (Nat.Primrec.const 1) hj) (Nat.Primrec.const 1) hj)
    (primrec_selectFn (primrec_sub₂ (Nat.Primrec.const 1) hj)
      (hpackT (primrec_sub₂ (Nat.Primrec.const 1) hi) (Nat.Primrec.const 1) hi)
      (primrec_selectFn (primrec_mod2.comp hi)
        (primrec_selectFn (primrec_mod2.comp hj) hleaf hzero)
        (primrec_selectFn (primrec_mod2.comp hj) hzero hnode)))).of_eq fun p => rfl

end Proposition77

end DomainTheory.NeighbourhoodSystems
