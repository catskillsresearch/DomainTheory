/-ai
For a computable presentation, together with primitive-recursive consistency, inclusion, and equality characteristics of the function space, the fixed-point combinator is a computable map from the function-space presentation to the presentation. Its neighbourhood relation is the recursively enumerable existential over chains of the decidable least-map step.

The function-space presentation supplies a primitive-recursive inclusion characteristic of enumerated neighbourhoods. Search for a list code whose chain characteristic has second component 1 and whose last index is accepted by the domain inclusion characteristic. That predicate is decidable because the chain characteristic and the inclusion characteristic are primitive recursive, by composing projections and comparing with the constant 1. It enumerates the relation because the chain form of the relation, the round trip of list coding, the read-off of the chain characteristic, and the equivalence of the decidable chain predicate with the least-map steps match a witnessing chain with its code and a witnessing code with its decoded chain.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.fixMap_rel_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.chainDec_iff_gStepsOK
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.primrec_fixChainChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.fixChainChar_spec

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}


variable (P : ComputablePresentation V)


/-- **Theorem 7.6 (Scott 1981, PRG-19) — `fix` is computable (choice-free).** For any effectively
given domain `𝒟` (here a computable presentation `P` of `V`, together with the function-space
consistency/inclusion/equality chars of Theorem 7.5), the combinator `fix : (𝒟 → 𝒟) → 𝒟` is
computable: its neighbourhood relation is the recursively-enumerable existential `∃ chain` over the
decidable least-map step relation. -/
theorem fixMap_isComputable
    (gN incl eq : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
      : Set (ApproximableMap V V)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2) (hinclp : Nat.Primrec incl)
    (heq : ∀ s, eq s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2) (heqp : Nat.Primrec eq) :
    ComputableMap
      (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp) P
      (fixMap V) := by
  constructor
  obtain ⟨fincl, hfinclp, hfincls⟩ :=
    (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp).incl_computable
  have hfincl : ∀ s, fincl s = 1 ↔ Xenum P P gN s.unpair.1 ⊆ Xenum P P gN s.unpair.2 :=
    fun s => (hfincls s).symm
  show REPred₂ (fun c ℓ => (fixMap V).rel (Xenum P P gN c) (P.X ℓ))
  refine ⟨fun w =>
      (fixChainChar P fincl w.unpair.2.unpair.1 w.unpair.1).unpair.2 = 1
      ∧ incl (Nat.pair (fixChainChar P fincl w.unpair.2.unpair.1 w.unpair.1).unpair.1
          w.unpair.2.unpair.2) = 1,
    ?_, ?_⟩
  · -- the search predicate is recursively decidable.
    have hcc : Nat.Primrec (fun w => fixChainChar P fincl w.unpair.2.unpair.1 w.unpair.1) :=
      ((primrec_fixChainChar P fincl hfinclp).comp
        ((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left)).of_eq (fun w => by
          simp only [unpair_pair_fst, unpair_pair_snd])
    have hA : Nat.Primrec (fun w =>
        (fixChainChar P fincl w.unpair.2.unpair.1 w.unpair.1).unpair.2) :=
      Nat.Primrec.right.comp hcc
    have hB : Nat.Primrec (fun w => incl (Nat.pair
        (fixChainChar P fincl w.unpair.2.unpair.1 w.unpair.1).unpair.1 w.unpair.2.unpair.2)) :=
      hinclp.comp ((Nat.Primrec.left.comp hcc).pair (Nat.Primrec.right.comp Nat.Primrec.right))
    exact (RecDecidable.natEq hA (Nat.Primrec.const 1)).and
      (RecDecidable.natEq hB (Nat.Primrec.const 1))
  · -- the search predicate enumerates `fix`'s neighbourhood relation.
    intro t
    show (fixMap V).rel (Xenum P P gN t.unpair.1) (P.X t.unpair.2) ↔ _
    rw [fixMap_rel_iff P gN hgN t.unpair.1 t.unpair.2]
    constructor
    · rintro ⟨full, hsteps, hlast⟩
      refine ⟨encodeList full, ?_⟩
      simp only [unpair_pair_fst, unpair_pair_snd]
      have hdec : decodeList (encodeList full) = full := decodeList_encodeList full
      obtain ⟨hfst, hsnd⟩ := fixChainChar_spec P fincl t.unpair.1 (encodeList full)
      rw [hdec] at hfst hsnd
      refine ⟨hsnd.mpr
        ((chainDec_iff_gStepsOK P gN hgN fincl hfincl t.unpair.1 full P.masterIdx).mpr hsteps), ?_⟩
      rw [hfst, hincl, unpair_pair_fst, unpair_pair_snd]
      exact hlast
    · rintro ⟨i, hi⟩
      simp only [unpair_pair_fst, unpair_pair_snd] at hi
      obtain ⟨hi1, hi2⟩ := hi
      obtain ⟨hfst, hsnd⟩ := fixChainChar_spec P fincl t.unpair.1 i
      refine ⟨decodeList i, ?_, ?_⟩
      · exact (chainDec_iff_gStepsOK P gN hgN fincl hfincl t.unpair.1 (decodeList i)
          P.masterIdx).mp (hsnd.mp hi1)
      · rw [← hfst]
        have hi2' := (hincl (Nat.pair (fixChainChar P fincl t.unpair.1 i).unpair.1
          t.unpair.2)).mp hi2
        rwa [unpair_pair_fst, unpair_pair_snd] at hi2'

end DomainTheory.NeighbourhoodSystems
