module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₀_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₁_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPaired_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.fiber_iterEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterIdx_ge
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterEnum_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterEnum_inter_eq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.interG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterInter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterInter_idx_lt
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterInter_idx_ge
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterEnum_cons_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.exists_list_fiber
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.primrec_iterIdx_proj
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.primrec_interG

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

/-- **Exercise 7.15 (Scott 1981, PRG-19) — `D^∞` carries a full computable presentation.** Built
choice-free from a presentation `P` of `V`: the enumeration codes finite fiber-index lists, the two
relations reduce to bounded coordinate checks (`RecDecidable.bForall`), and the intersection function
tabulates `P.inter` coordinate-wise. -/
noncomputable def iterPresentation (P : ComputablePresentation V) :
    ComputablePresentation (iterSys V) where
  X := iterEnum P
  mem_X := iterEnum_mem
  surj := by
    rintro W hW
    obtain ⟨N, hN⟩ := hW.2
    obtain ⟨L, hlen, hL⟩ := exists_list_fiber (P := P) hW N
    refine ⟨encodeList L, ?_⟩
    apply eq_of_fiber_eq
    intro j
    show P.X (nthCode (encodeList L) j P.masterIdx) = fiber W j
    rw [nthCode_eq, decodeList_encodeList]
    by_cases hj : j < N
    · exact hL j hj
    · rw [getD_eq_default_cf L P.masterIdx (by rw [hlen]; omega), P.masterIdx_spec,
        hN j (by omega)]
  interEq_computable := by
    have hbound : Nat.Primrec
        (fun t : ℕ => t.unpair.1 + t.unpair.2.unpair.1 + t.unpair.2.unpair.2) :=
      primrec_add₂ (primrec_add₂ Nat.Primrec.left (Nat.Primrec.left.comp Nat.Primrec.right))
        (Nat.Primrec.right.comp Nat.Primrec.right)
    have hA : Nat.Primrec (fun w => iterIdx P w.unpair.2.unpair.1 w.unpair.1) :=
      primrec_iterIdx_proj (Nat.Primrec.left.comp Nat.Primrec.right)
    have hB : Nat.Primrec (fun w => iterIdx P w.unpair.2.unpair.2.unpair.1 w.unpair.1) :=
      primrec_iterIdx_proj (Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right))
    have hC : Nat.Primrec (fun w => iterIdx P w.unpair.2.unpair.2.unpair.2 w.unpair.1) :=
      primrec_iterIdx_proj (Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right))
    have hq : RecDecidable (fun w => P.X (iterIdx P w.unpair.2.unpair.1 w.unpair.1)
        ∩ P.X (iterIdx P w.unpair.2.unpair.2.unpair.1 w.unpair.1)
        = P.X (iterIdx P w.unpair.2.unpair.2.unpair.2 w.unpair.1)) := by
      refine RecDecidable.of_iff (fun w => ?_) (P.interEq_computable.comp (hA.pair (hB.pair hC)))
      simp only [unpair_pair_fst, unpair_pair_snd]
    refine RecDecidable.of_iff (fun t => ?_) (hq.bForall hbound)
    simp only [unpair_pair_fst, unpair_pair_snd]
    exact iterEnum_inter_eq_iff
  cons_computable := by
    have hbound : Nat.Primrec (fun t : ℕ => t.unpair.1 + t.unpair.2) :=
      primrec_add₂ Nat.Primrec.left Nat.Primrec.right
    have hA : Nat.Primrec (fun w => iterIdx P w.unpair.2.unpair.1 w.unpair.1) :=
      primrec_iterIdx_proj (Nat.Primrec.left.comp Nat.Primrec.right)
    have hB : Nat.Primrec (fun w => iterIdx P w.unpair.2.unpair.2 w.unpair.1) :=
      primrec_iterIdx_proj (Nat.Primrec.right.comp Nat.Primrec.right)
    have hq : RecDecidable (fun w => ∃ i, P.X i ⊆ P.X (iterIdx P w.unpair.2.unpair.1 w.unpair.1)
        ∩ P.X (iterIdx P w.unpair.2.unpair.2 w.unpair.1)) := by
      refine RecDecidable.of_iff (fun w => ?_) (P.cons_computable.comp (hA.pair hB))
      simp only [unpair_pair_fst, unpair_pair_snd]
    refine RecDecidable.of_iff (fun t => ?_) (hq.bForall hbound)
    simp only [unpair_pair_fst, unpair_pair_snd]
    exact iterEnum_cons_iff
  inter := iterInter P
  inter_primrec := by
    have hr : Nat.Primrec (fun t => Nat.pair
        (Nat.pair (t.unpair.1 + t.unpair.2) (Nat.pair t.unpair.1 t.unpair.2))
        (t.unpair.1 + t.unpair.2)) :=
      ((primrec_add₂ Nat.Primrec.left Nat.Primrec.right).pair
        (Nat.Primrec.left.pair Nat.Primrec.right)).pair
        (primrec_add₂ Nat.Primrec.left Nat.Primrec.right)
    refine ((primrec_tabCode (primrec_interG (P := P))).comp hr).of_eq (fun t => ?_)
    show tabCode (interG P) _ _ = iterInter P t.unpair.1 t.unpair.2
    unfold iterInter
    simp only [unpair_pair_fst, unpair_pair_snd]
  inter_spec := by
    intro n m hcons
    apply eq_of_fiber_eq
    intro j
    rw [fiber_inter, fiber_iterEnum, fiber_iterEnum, fiber_iterEnum]
    by_cases hj : j < n + m
    · rw [iterInter_idx_lt hj, P.inter_spec ((iterEnum_cons_iff (P := P)).mp hcons j hj)]
    · rw [iterInter_idx_ge (by omega), iterIdx_ge (show n ≤ j by omega),
        iterIdx_ge (show m ≤ j by omega), P.masterIdx_spec, Set.inter_self]
  masterIdx := 0
  masterIdx_spec := by
    apply eq_of_fiber_eq
    intro j
    rw [fiber_iterEnum, fiber_iterSys_master, iterIdx_ge (Nat.zero_le j), P.masterIdx_spec]

end Iterate

end DomainTheory.NeighbourhoodSystems
