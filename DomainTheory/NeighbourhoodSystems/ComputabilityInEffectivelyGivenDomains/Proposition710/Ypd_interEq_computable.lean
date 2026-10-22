module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.eqCode_computable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.interCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_interCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.primrec_interCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- **Scott's relation (i):** `Y_n ∩ Y_m = Y_k` is recursively decidable, by reducing to the equality
decider via the (primitive-recursive) intersection code. -/
theorem Ypd_interEq_computable (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons)
    (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    RecDecidable₃ (fun n m k => V.Ypd P n ∩ V.Ypd P m = V.Ypd P k) := by
  have hic : Nat.Primrec (fun t => V.interCode P cons t.unpair.1 t.unpair.2.unpair.1) :=
    ((V.primrec_interCode P cons hconsp).comp
      (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right))).of_eq
      (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
  have hg : Nat.Primrec
      (fun t => Nat.pair (V.interCode P cons t.unpair.1 t.unpair.2.unpair.1) t.unpair.2.unpair.2) :=
    hic.pair (Nat.Primrec.right.comp Nat.Primrec.right)
  refine RecDecidable.of_iff (fun t => ?_) ((V.eqCode_computable P).comp hg)
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [V.Ypd_interCode P cons t.unpair.1 t.unpair.2.unpair.1 hcons]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
