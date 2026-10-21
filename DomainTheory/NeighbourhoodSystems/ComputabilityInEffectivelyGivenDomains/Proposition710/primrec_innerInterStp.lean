/-ai
If the consistency function is primitive recursive, then the inner intersection step is primitive recursive.

The three unpairing projections are primitive recursive, as are the pairing of the outer index with the current index, the consistency test of that pair, and the intersection index of that pair, the last by the presentation's primitive-recursive intersection after the pairing identity. The successor of the pair of that intersection index with the accumulator is primitive recursive. The step is the primitive-recursive selection between this prepended code and the accumulator according to whether the consistency value is one, and that selection is the inner step.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.innerInterStp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

theorem primrec_innerInterStp (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons) :
    Nat.Primrec (V.innerInterStp P cons) := by
  have h1 : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have ha : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hpair_ab : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.2 w.unpair.1) := ha.pair h1
  have hcons_ab : Nat.Primrec (fun w : ℕ => cons (Nat.pair w.unpair.2.unpair.2 w.unpair.1)) :=
    hconsp.comp hpair_ab
  have hinter_ab : Nat.Primrec (fun w : ℕ => P.inter w.unpair.2.unpair.2 w.unpair.1) :=
    (P.inter_primrec.comp hpair_ab).of_eq (fun w => by simp only [unpair_pair_fst, unpair_pair_snd])
  have hprepend : Nat.Primrec
      (fun w : ℕ => Nat.pair (P.inter w.unpair.2.unpair.2 w.unpair.1) w.unpair.2.unpair.1 + 1) :=
    Nat.Primrec.succ.comp (hinter_ab.pair hacc)
  exact (primrec_selectFn (primrec_isOne.comp hcons_ab) hprepend hacc).of_eq (fun _ => rfl)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
