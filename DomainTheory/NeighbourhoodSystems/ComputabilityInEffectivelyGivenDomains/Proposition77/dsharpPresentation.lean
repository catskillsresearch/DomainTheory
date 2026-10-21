/-ai
Given a computable presentation of a neighbourhood system D in which every neighbourhood is nonempty, dsharpPresentation is the computable presentation of the sharp system whose tokens are the sharp neighbourhoods, whose consistency decider and whose equality-of-intersection decider are the consistency bit and the product of that bit with an equality bit of the course-of-values value of the sharp decider step built from D's deciders, whose intersection index is the intersection component of that value computed with dummy consistency and equality functions, and whose master index is zero.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_surj
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.primrec_gOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.primrec_dsharpStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharp_decider_spec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharp_intI_correct
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharp_interEq_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

/-- **Proposition 7.7 (Scott 1981, PRG-19).** A computable presentation of `D^§` from one of `D`. -/
def dsharpPresentation (hD : ∀ X, D.mem X → X.Nonempty) :
    ComputablePresentation (Dsharp D hD) where
  X := Vsharp D P
  mem_X := fun n => Vsharp_mem P n
  surj := fun hY => Vsharp_surj P hY
  interEq_computable := by
    obtain ⟨fc, hfc_pr, hfc⟩ := P.cons_computable
    obtain ⟨fe, hfe_pr, hfe⟩ := P.eq_computable
    have hcons : ∀ a b, fc (Nat.pair a b) = 1 ↔ ∃ l, P.X l ⊆ P.X a ∩ P.X b := fun a b => by
      have := hfc (Nat.pair a b); simp only [unpair_pair_fst, unpair_pair_snd] at this; exact this.symm
    have heq : ∀ a b, fe (Nat.pair a b) = 1 ↔ P.X a = P.X b := fun a b => by
      have := hfe (Nat.pair a b); simp only [unpair_pair_fst, unpair_pair_snd] at this; exact this.symm
    have hinter : ∀ a b, (∃ l, P.X l ⊆ P.X a ∩ P.X b) →
        P.X ((fun s => P.inter s.unpair.1 s.unpair.2) (Nat.pair a b)) = P.X a ∩ P.X b := fun a b h => by
      simp only [unpair_pair_fst, unpair_pair_snd]; exact P.inter_spec h
    refine ⟨fun t => consB (gOf (dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2))
        (Nat.pair t.unpair.1 t.unpair.2.unpair.1))
        * eqB (gOf (dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2))
            (Nat.pair (intI (gOf (dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2))
              (Nat.pair t.unpair.1 t.unpair.2.unpair.1))) t.unpair.2.unpair.2)), ?_, fun t => ?_⟩
    · have hg := primrec_gOf (primrec_dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2)
        hfc_pr hfe_pr P.inter_primrec)
      have hc0 := hg.comp (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right))
      exact primrec_mul₂ ((Nat.Primrec.left.comp Nat.Primrec.right).comp hc0)
        (Nat.Primrec.left.comp (hg.comp
          (((Nat.Primrec.right.comp Nat.Primrec.right).comp hc0).pair
            (Nat.Primrec.right.comp Nat.Primrec.right))))
    · exact dsharp_interEq_iff P fc fe (fun s => P.inter s.unpair.1 s.unpair.2) hD hcons heq hinter
        t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2
  cons_computable := by
    obtain ⟨fc, hfc_pr, hfc⟩ := P.cons_computable
    obtain ⟨fe, hfe_pr, hfe⟩ := P.eq_computable
    have hcons : ∀ a b, fc (Nat.pair a b) = 1 ↔ ∃ l, P.X l ⊆ P.X a ∩ P.X b := fun a b => by
      have := hfc (Nat.pair a b); simp only [unpair_pair_fst, unpair_pair_snd] at this; exact this.symm
    have heq : ∀ a b, fe (Nat.pair a b) = 1 ↔ P.X a = P.X b := fun a b => by
      have := hfe (Nat.pair a b); simp only [unpair_pair_fst, unpair_pair_snd] at this; exact this.symm
    have hinter : ∀ a b, (∃ l, P.X l ⊆ P.X a ∩ P.X b) →
        P.X ((fun s => P.inter s.unpair.1 s.unpair.2) (Nat.pair a b)) = P.X a ∩ P.X b := fun a b h => by
      simp only [unpair_pair_fst, unpair_pair_snd]; exact P.inter_spec h
    refine ⟨fun t => consB (gOf (dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2))
        (Nat.pair t.unpair.1 t.unpair.2)), ?_, fun t => ?_⟩
    · have hg := primrec_gOf (primrec_dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2)
        hfc_pr hfe_pr P.inter_primrec)
      exact (Nat.Primrec.left.comp Nat.Primrec.right).comp
        (hg.comp (Nat.Primrec.left.pair Nat.Primrec.right))
    · exact (dsharp_decider_spec P fc fe (fun s => P.inter s.unpair.1 s.unpair.2) hD hcons heq hinter
        t.unpair.1 t.unpair.2).1.symm
  inter := fun n m => intI (gOf (dsharpStep (fun _ => 0) (fun _ => 0)
    (fun s => P.inter s.unpair.1 s.unpair.2)) (Nat.pair n m))
  inter_primrec := by
    have hg := primrec_gOf (primrec_dsharpStep (fun _ => 0) (fun _ => 0)
      (fun s => P.inter s.unpair.1 s.unpair.2) (Nat.Primrec.const 0) (Nat.Primrec.const 0)
      P.inter_primrec)
    have hpair : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 t.unpair.2) :=
      Nat.Primrec.left.pair Nat.Primrec.right
    exact (Nat.Primrec.right.comp Nat.Primrec.right).comp (hg.comp hpair)
  inter_spec := by
    intro n m h
    exact dsharp_intI_correct P (fun _ => 0) (fun _ => 0) (fun s => P.inter s.unpair.1 s.unpair.2) hD
      (fun a b hh => by simp only [unpair_pair_fst, unpair_pair_snd]; exact P.inter_spec hh) n m h
  masterIdx := 0
  masterIdx_spec := Vsharp_zero P

end Proposition77

end DomainTheory.NeighbourhoodSystems
