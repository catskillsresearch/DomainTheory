/-ai
The forward reindexing map is computable, and in fact recursively decidable. On codes, its relation is a nested bounded universal quantification of the inclusion decider.

The two iterated index expressions compared by inclusion are primitive recursive, so the inclusion predicate is recursively decidable. Bounded universal quantification over the inner iterated index, and then over the outer code, remains recursively decidable. Rewriting by the enumeration presentation and the bounded characterisation of the relation shows that this predicate decides the relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_rel_enum_iff

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashMap_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProju2080_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProju2081_isComputable
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

variable (P : ComputablePresentation V)

variable {P}

/-- **`F` is computable** (in fact recursively decidable): its index relation reduces to a nested
bounded `∀` of `incl_computable`. -/
theorem Fmap_isComputable :
    ComputableMap (iterPresentation P) (iterPresentation (iterPresentation P)) (Fmap V) := by
  constructor
  -- inner predicate `p₂ u`, with `u = ⟨j, ⟨i, ⟨n, m⟩⟩⟩`
  have hLHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P u.unpair.2.unpair.2.unpair.1 (Nat.pair u.unpair.2.unpair.1 u.unpair.1)) := by
    refine (primrec_nthCode.comp
      ((Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)).pair
        (((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left).pair
          (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hRHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.2.unpair.2 u.unpair.2.unpair.1)
        u.unpair.1) := by
    have hinner : Nat.Primrec (fun u : ℕ =>
        iterIdx (iterPresentation P) u.unpair.2.unpair.2.unpair.2 u.unpair.2.unpair.1) := by
      refine (primrec_nthCode.comp
        ((Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)).pair
          ((Nat.Primrec.left.comp Nat.Primrec.right).pair
            (Nat.Primrec.const (iterPresentation P).masterIdx)))).of_eq (fun u => ?_)
      simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
    refine (primrec_nthCode.comp
      (hinner.pair (Nat.Primrec.left.pair (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hp₂ : RecDecidable (fun u : ℕ =>
      P.X (iterIdx P u.unpair.2.unpair.2.unpair.1 (Nat.pair u.unpair.2.unpair.1 u.unpair.1))
        ⊆ P.X (iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.2.unpair.2
          u.unpair.2.unpair.1) u.unpair.1)) := by
    refine RecDecidable.of_iff (fun u => ?_) (P.incl_computable.comp (hLHS.pair hRHS))
    simp only [unpair_pair_fst, unpair_pair_snd]
  -- inner bound `bound₂ v = iterIdx (iterᴾ) m i`, with `v = ⟨i, ⟨n, m⟩⟩`
  have hbound₂ : Nat.Primrec (fun v : ℕ =>
      iterIdx (iterPresentation P) v.unpair.2.unpair.2 v.unpair.1) := by
    refine (primrec_nthCode.comp
      ((Nat.Primrec.right.comp Nat.Primrec.right).pair
        (Nat.Primrec.left.pair (Nat.Primrec.const (iterPresentation P).masterIdx)))).of_eq
      (fun v => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hbound₁ : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hp₁ := hp₂.bForall hbound₂
  have hp₀ := hp₁.bForall hbound₁
  refine (RecDecidable.of_iff (fun t => ?_) hp₀).re
  -- match the relation with the nested bounded `∀`
  simp only [iterPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact Fmap_rel_enum_iff t.unpair.1 t.unpair.2

end Exercise718

end DomainTheory.NeighbourhoodSystems
