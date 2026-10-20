module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.primrec_untagList
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.primrec_untagVal
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_GraphIdx_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.forall_rel_iff_subset_step

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)










































































/-- **`j ∈ GraphIdx (Xenum … c)` is recursively enumerable, jointly in `(c, j)`.** Unfolds via
`mem_GraphIdx_iff`/`forall_rel_iff_subset_step`/`Xenum_singleton` to `∃ n m₀, <primitive-recursive
check> ∧ Xenum … c ⊆ Xenum … (pair (pair n m₀) 0 + 1) ∧ <bit test>` — a decidable body existentially
quantified over the two witnesses `n, m₀` (`REPred.proj`, applied twice). -/
theorem graphIdx_isComputable (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf PNpres PNpres (decodeList c))
      : Set (ApproximableMap PN PN)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ PNpres.X s.unpair.1 ⊆ PNpres.X s.unpair.2)
    (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ PNpres.X s.unpair.1 ⊆ PNpres.X s.unpair.2)
    (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ PNpres.X s.unpair.1 = PNpres.X s.unpair.2) (heq1p : Nat.Primrec eq1) :
    REPred₂ (fun c j => j ∈ GraphIdx
      (Xenum PNpres PNpres gN c : Set (ApproximableMap PN PN))) := by
  have hinclP : RecDecidable₂ (fun a b =>
      (Xenum PNpres PNpres gN a : Set (ApproximableMap PN PN)) ⊆ Xenum PNpres PNpres gN b) :=
    (funPresentation PNpres PNpres gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p hincl1 hincl1p heq1
      heq1p).incl_computable
  -- packed `w = ⟨m₀, ⟨n, ⟨c, j⟩⟩⟩`; the base predicate is decidable in `w`.
  have hj : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hm0 : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hbitsCodeArg : Nat.Primrec (fun w : ℕ => bitsCode w.unpair.2.unpair.1 w.unpair.2.unpair.1) :=
    (primrec_bitsCode.comp (hn.pair hn)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hpairArg : Nat.Primrec
      (fun w : ℕ => Nat.pair (Nat.pair w.unpair.2.unpair.1 w.unpair.1) 0 + 1) :=
    Nat.Primrec.succ.comp ((hn.pair hm0).pair (Nat.Primrec.const 0))
  have hA : RecDecidable (fun w : ℕ =>
      untagList w.unpair.2.unpair.2.unpair.2 =
        bitsCode w.unpair.2.unpair.1 w.unpair.2.unpair.1) :=
    RecDecidable.natEq (primrec_untagList.comp hj) hbitsCodeArg
  have hB : RecDecidable (fun w : ℕ =>
      (Xenum PNpres PNpres gN w.unpair.2.unpair.2.unpair.1 : Set (ApproximableMap PN PN)) ⊆
        Xenum PNpres PNpres gN (Nat.pair (Nat.pair w.unpair.2.unpair.1 w.unpair.1) 0 + 1)) :=
    RecDecidable.of_iff (fun w => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hinclP.comp (hc.pair hpairArg))
  have hC : RecDecidable (fun w : ℕ =>
      w.unpair.1.testBit (untagVal w.unpair.2.unpair.2.unpair.2) = true) :=
    ⟨fun w => bitAt w.unpair.1 (untagVal w.unpair.2.unpair.2.unpair.2),
      (primrec_bitAt.comp (hm0.pair (primrec_untagVal.comp hj))).of_eq fun w => by
        simp only [unpair_pair_fst, unpair_pair_snd],
      fun w => (bitAt_eq_one_iff _ _).symm⟩
  have hre : REPred (fun w : ℕ =>
      untagList w.unpair.2.unpair.2.unpair.2 =
        bitsCode w.unpair.2.unpair.1 w.unpair.2.unpair.1 ∧
      (Xenum PNpres PNpres gN w.unpair.2.unpair.2.unpair.1 : Set (ApproximableMap PN PN)) ⊆
        Xenum PNpres PNpres gN (Nat.pair (Nat.pair w.unpair.2.unpair.1 w.unpair.1) 0 + 1) ∧
      w.unpair.1.testBit (untagVal w.unpair.2.unpair.2.unpair.2) = true) :=
    (hA.and (hB.and hC)).re
  have hp2 := hre.proj.proj
  refine REPred.of_iff (fun t => ?_) hp2
  dsimp only
  rw [mem_GraphIdx_iff]
  constructor
  · rintro ⟨n, m₀, heq, hf, hbit⟩
    refine ⟨n, m₀, ?_⟩
    show untagList (Nat.pair m₀ (Nat.pair n t)).unpair.2.unpair.2.unpair.2 =
          bitsCode (Nat.pair m₀ (Nat.pair n t)).unpair.2.unpair.1
            (Nat.pair m₀ (Nat.pair n t)).unpair.2.unpair.1 ∧
        (Xenum PNpres PNpres gN (Nat.pair m₀ (Nat.pair n t)).unpair.2.unpair.2.unpair.1
          : Set (ApproximableMap PN PN)) ⊆
          Xenum PNpres PNpres gN (Nat.pair
            (Nat.pair (Nat.pair m₀ (Nat.pair n t)).unpair.2.unpair.1
              (Nat.pair m₀ (Nat.pair n t)).unpair.1) 0 + 1) ∧
        (Nat.pair m₀ (Nat.pair n t)).unpair.1.testBit
          (untagVal (Nat.pair m₀ (Nat.pair n t)).unpair.2.unpair.2.unpair.2) = true
    simp only [unpair_pair_fst, unpair_pair_snd]
    refine ⟨heq, ?_, hbit⟩
    rw [Xenum_singleton PNpres PNpres gN hgN n m₀]
    exact forall_rel_iff_subset_step.mp hf
  · rintro ⟨n, m₀, hbase⟩
    simp only [unpair_pair_fst, unpair_pair_snd] at hbase
    obtain ⟨heq, hsub, hbit⟩ := hbase
    refine ⟨n, m₀, heq, ?_, hbit⟩
    apply forall_rel_iff_subset_step.mpr
    rwa [Xenum_singleton PNpres PNpres gN hgN n m₀] at hsub

end DomainTheory.NeighbourhoodSystems.Exercise723
