module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_rel_enum_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

variable (P : ComputablePresentation V)

variable {P}

/-- **`G` is computable** (in fact recursively decidable): a single bounded `∀` of `incl_computable`. -/
theorem Gmap_isComputable :
    IsComputableMap (iterPresentation (iterPresentation P)) (iterPresentation P) (Gmap V) := by
  -- inner predicate `p₂ u`, with `u = ⟨k, ⟨s, n⟩⟩`
  have hLHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.1 u.unpair.1.unpair.1)
        u.unpair.1.unpair.2) := by
    have hinner : Nat.Primrec (fun u : ℕ =>
        iterIdx (iterPresentation P) u.unpair.2.unpair.1 u.unpair.1.unpair.1) := by
      refine (primrec_nthCode.comp
        ((Nat.Primrec.left.comp Nat.Primrec.right).pair
          ((Nat.Primrec.left.comp Nat.Primrec.left).pair
            (Nat.Primrec.const (iterPresentation P).masterIdx)))).of_eq (fun u => ?_)
      simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
    refine (primrec_nthCode.comp
      (hinner.pair ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hRHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P u.unpair.2.unpair.2 u.unpair.1) := by
    refine (primrec_nthCode.comp
      ((Nat.Primrec.right.comp Nat.Primrec.right).pair
        (Nat.Primrec.left.pair (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hp₂ : RecDecidable (fun u : ℕ =>
      P.X (iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.1 u.unpair.1.unpair.1)
        u.unpair.1.unpair.2) ⊆ P.X (iterIdx P u.unpair.2.unpair.2 u.unpair.1)) := by
    refine RecDecidable.of_iff (fun u => ?_) (P.incl_computable.comp (hLHS.pair hRHS))
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hbound₁ : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hp₀ := hp₂.bForall hbound₁
  refine (RecDecidable.of_iff (fun t => ?_) hp₀).re
  simp only [iterPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact Gmap_rel_enum_iff t.unpair.1 t.unpair.2

end Exercise718

end DomainTheory.NeighbourhoodSystems
