module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86c.subApprox_rel_Xenum_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86c.sub_leastMap_rel_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86c.subStep_recDecidable

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6

variable {α : Type*} {E : NeighborhoodSystem α}


section SubComputable

variable (P : ComputablePresentation E) (gN : ℕ → ℕ)
  (hgN : ∀ c, gN c = 1 ↔
    (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty)


/-- **Theorem 8.6(c) (Scott 1981, PRG-19), as an `ComputableMap` statement.** Relative to the
function-space presentation `funPresentation P P …` (Theorem 7.5) built from any presentation `P` of
`E`, `subApprox` is computable: its neighbourhood relation is the recursively enumerable
`¬(consistent m) ∨ ∀ e ∈ decodeList m, ∃ y, …` (a bounded `∀` of an unbounded `∃` of a decidable
predicate). -/
theorem subApprox_isComputable
    (incl eq : ℕ → ℕ)
    (hgNp : Nat.Primrec gN)
    (hincl : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2) (hinclp : Nat.Primrec incl)
    (heq : ∀ s, eq s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2) (heqp : Nat.Primrec eq) :
    ComputableMap
      (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp)
      (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp)
      (subApprox (E := E)) := by
  constructor
  obtain ⟨fincl, hfinclp, hfincls⟩ :=
    (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp).incl_computable
  have hfincl : ∀ s, fincl s = 1 ↔ Xenum P P gN s.unpair.1 ⊆ Xenum P P gN s.unpair.2 :=
    fun s => (hfincls s).symm
  show REPred₂ (fun n m => (subApprox (E := E)).rel (Xenum P P gN n) (Xenum P P gN m))
  have hdec := subStep_recDecidable P gN fincl incl hfincl hfinclp hincl hinclp
  have hre : REPred₂ (fun n e => ∃ y : ℕ,
      Xenum P P gN n ⊆ Xenum P P gN (codePair y y) ∧
        P.X e.unpair.1 ⊆ P.X y ∧ P.X y ⊆ P.X e.unpair.2) := by
    refine REPred.of_iff (fun t => ?_) hdec.re.proj
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hforall : REPred (fun t => ∀ e ∈ decodeList t.unpair.2, ∃ y : ℕ,
      Xenum P P gN t.unpair.1 ⊆ Xenum P P gN (codePair y y) ∧
        P.X e.unpair.1 ⊆ P.X y ∧ P.X y ⊆ P.X e.unpair.2) :=
    REPred.forall_mem_decodeList₂ hre
  have hne1 : REPred (fun t => ¬ gN t.unpair.2 = 1) :=
    ((RecDecidable.natEq (hgNp.comp Nat.Primrec.right) (Nat.Primrec.const 1)).not).re
  refine REPred.of_iff (fun t => ?_) (hne1.or hforall)
  show (subApprox (E := E)).rel (Xenum P P gN t.unpair.1) (Xenum P P gN t.unpair.2) ↔ _
  rw [subApprox_rel_Xenum_iff P gN hgN t.unpair.1 t.unpair.2, Decidable.imp_iff_not_or]
  refine or_congr_right (forall_congr' (fun e => imp_congr_right (fun _ => ?_)))
  exact sub_leastMap_rel_iff P gN hgN t.unpair.1 e.unpair.1 e.unpair.2

end SubComputable
end DomainTheory.NeighbourhoodSystems
